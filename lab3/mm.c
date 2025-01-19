
// 计算机系统概论实验3：malloc lab
// 完成人：王浩然
// 学号：2022010229
// 日期：2023年12月13日，大雪

#include "memlib.h"
#include "mm.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

team_t team = {
    "UBEC-THUCST2",
    "王浩然", // 姓名
    "2022010229", // 学号
    "",
    "" 
};

/********** 宏定义起始 **********/ 
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

#define ALIGNMENT 16 // 对齐位数，C语言在64位系统上默认16位对齐
#define WSIZE 8 // `字`的字节数，与header, footer相同 
#define DSIZE 16 // `双字`的字节数

#define ALLOCATED 1 // 当前块已分配
#define FREE 0 // 当前块未分配

#define SEG_LEN 15 // 分类大小类数目
#define CHUNKSIZE (1 << 13) // 默认堆扩展字节数

#define ALIGN(size) ((size) <= DSIZE) ? 2 * DSIZE : ((size) + 2 * DSIZE) & ~(ALIGNMENT - 1) // 分配大小16位对齐

#define GET(p) (*(size_t*)(p)) // 获取p处指针
#define PUT(p, val) (*(size_t*)(p) = (val)) // 写入p处指针 
#define GET_SIZE(p) (GET(p) & ~(ALIGNMENT - 1)) // 获取p所在块大小 
#define GET_ALLOC(p) (GET(p) & 0x1) // 获取p所在块分配情况
#define PACK(size, alloc) ((size) | (alloc)) // 设置大小及分配情况 

#define HDRP(bp) ((char *)(bp) - WSIZE) // 获取块的header
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 获取块的footer

#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 获取上一块的大小
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp))) // 获取下一块的大小

#define CUR_SIZE(bp) GET_SIZE(HDRP(bp)) // 获取当前块大小
#define PREV_SIZE(bp) GET_SIZE(HDRP(PREV_BLKP(bp))) // 获取上一块大小
#define NEXT_SIZE(bp) GET_SIZE(HDRP(NEXT_BLKP(bp))) // 获取下一块大小

#define PRED(bp) ((char *)(bp) + WSIZE) // 获取当前segregated_list中上一块地址
#define SUCC(bp) ((char *)(bp)) // 获取当前segregated_list中下一块地址

#define PRED_BLKP(bp) (GET(PRED(bp))) // 获取物理意义中上一块地址
#define SUCC_BLKP(bp) (GET(SUCC(bp))) // 获取物理意义中下一块地址
/********** 宏定义结束 **********/

/********** 函数声明起始 **********/
static int get_index(size_t); // 获取大小类索引
static void insert_free_block(char*);
static void delete_free_block(char*);
static void *extend_heap(size_t); // 扩展堆
static void *coalesce(void*); // 合并空闲块
static void *find_fit(size_t, int); // 寻找合适空闲块
static void *place(char*, size_t); // 分配空闲块
int mm_init(void); // 初始化堆
void *mm_malloc(size_t); // 分配空间
void mm_free(void*); // 释放空间
void *mm_realloc(void*, size_t); // 重新分配空间
/********** 函数声明结束 **********/

/********** 全局变量起始 *********/
static char *heap_listp; // 堆开始地址
static char *segregated_listp; // 分类大小类头指针
/********** 全局变量结束 *********/

/********** 块结构起始 **********/
/*
                        A : 0表示当前块未分配，1表示当前块已分配
                                X : 未使用位，用于对齐 
         63  62  61  60  59  58  ... 10   9   8   7   6   5   4   3   2   1   0
        | - | - | - | - | - | - | - | - | - | - | - | - | - | - | - | - | - | - |
header->|              块的大小 64-4=0 bits, 63...4              | X | X | X | A |
  bp->  |                                                                       |
        |                                  ...                                  |
        |                                载荷部分                                |
        |                                  ...                                  |
footer->|              块的大小 64-4=0 bits, 63...4              | X | X | X | A |
        | - | - | - | - | - | - | - | - | - | - | - | - | - | - | - | - | - | - |
*/
/********** 块结构结束 **********/

/**
 * @brief 
 * 查找字节数对应segeragated_list索引
 * 实际上在计算log2, 但是O(1)
 * 参考 Sean Anderson: `Bit twiddling hacks`
 * https://graphics.stanford.edu/~seander/bithacks.html#IntegerLogLookup
 * @param v size_t，待获取组别的字节数
 * @return int，返回组别
 */
static inline int get_index(size_t v) {
    // Sean Anderson利用位运算计算log2过程
    // 原文基于32位整数，这里改为64位
    size_t r, shift;
    r     = (v > 0xffff) << 4; v >>= r;
    shift = (v > 0xff  ) << 3; v >>= shift; r |= shift;
    shift = (v > 0xf   ) << 2; v >>= shift; r |= shift;
    shift = (v > 0x3   ) << 1; v >>= shift; r |= shift;
                                            r |= (v >> 1);
    int x = r - 5;
    if(x < 0) x = 0; // 若当前大小类过小，归入最小大小类
    if(x >= SEG_LEN) x = SEG_LEN - 1; // 若当前大小类过大，归入最大大小类
    return x;
} 

/**
 * @brief
 * 将空闲块插入到对应大小类的链表中
 * @param bp char*，待插入空闲块地址
 * @return void
*/
static void insert_free_block(char *bp) {
    int seg = get_index(CUR_SIZE(bp)); // 获取当前大小类索引
    char *root = segregated_listp + seg * WSIZE; // 获取当前大小类头指针
    void *succ = root; // 获取当前大小类第一个空闲块地址
    while(SUCC_BLKP(succ)) {
        succ = (char*)SUCC_BLKP(succ);
        if((unsigned int)succ >= (unsigned int)bp)  {
            char *tmp = succ;
            succ = (char*)PRED_BLKP(succ);
            // 更新链表
            PUT(SUCC(succ), bp);
            PUT(PRED(bp), succ);
            PUT(SUCC(bp), tmp);
            PUT(PRED(tmp), bp);
            return;
        }
    }
    // 当前大小类无空闲块，或者在地址分配时当前空闲块地址最大，被分配在最后
    PUT(SUCC(succ), bp);
    PUT(PRED(bp), succ);
    PUT(SUCC(bp), NULL);
}

/**
 * @brief
 * 将空闲块从对应大小类的链表中删除
 * @param bp char*，待删除空闲块地址
 * @return void
*/
static void delete_free_block(char *bp) {
    int seg = get_index(CUR_SIZE(bp));
    if(SUCC_BLKP(bp) && PRED_BLKP(bp)) { // 前驱后继都有
        PUT(SUCC(PRED_BLKP(bp)), SUCC_BLKP(bp));
        PUT(PRED(SUCC_BLKP(bp)), PRED_BLKP(bp));
    } else if(PRED_BLKP(bp)) { // 只有前驱，是最后一块
        PUT(SUCC(PRED_BLKP(bp)), NULL);
    } else if(SUCC_BLKP(bp)) { // 只有后继，是最开始一块
        PUT(PRED(SUCC_BLKP(bp)), NULL);
    }
    // 无前驱后继
    PUT(SUCC(bp), NULL);
    PUT(PRED(bp), NULL);
}

/**
 * @brief
 * 调用mem_sbrk扩展堆
 * @param asize size_t，扩展字节数
 * @return void*，返回扩展后的堆地址
*/
static void *extend_heap(size_t asize) {
    char *bp;
    if((long)(bp = mem_sbrk(asize)) == -1) return NULL;
    // 初始化新空闲内存块
    PUT(HDRP(bp), PACK(asize, FREE));
    PUT(FTRP(bp), PACK(asize, FREE));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, ALLOCATED));
    return coalesce(bp); // 不要忘记合并，刚开始直接返回bp了...
}

/**
 * @brief
 * 合并空闲块
 * @param bp void*，待合并空闲块地址
 * @return void*, 合并后空闲块地址
*/
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); //获取地址前块标记
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); //获取地址后块标记
    size_t size = CUR_SIZE(bp); //初始化新空闲内存块大小

    if (prev_alloc && next_alloc) { // 前后块都已分配
        insert_free_block(bp);
        return bp;        
    } else if(prev_alloc && !next_alloc) { // 前块已分配，后块未分配
        size += NEXT_SIZE(bp); //更新内存块大小
        delete_free_block(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, FREE));
        PUT(FTRP(bp), PACK(size, FREE));
        PUT(PRED(bp), NULL);
        PUT(SUCC(bp), NULL); 
    } else if(!prev_alloc && next_alloc) { // 前块未分配，后块已分配
        size += PREV_SIZE(bp);
        delete_free_block(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, FREE));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, FREE));         
        // 注意，这里是不对称的。因为我们只能获取next块的大小，而不能获取prev块的大小
        bp = PREV_BLKP(bp);
        PUT(PRED(bp), NULL);
        PUT(SUCC(bp), NULL);        
    } else { // 前后块都未分配
        size += NEXT_SIZE(bp) + PREV_SIZE(bp);
        delete_free_block(PREV_BLKP(bp));
        delete_free_block(NEXT_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, FREE));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, FREE));
        bp = PREV_BLKP(bp);
        PUT(PRED(bp), NULL);
        PUT(SUCC(bp), NULL);
    }
    insert_free_block(bp);
    return bp;
}

/**
 * @brief
 * 查找合适空闲块
 * 采用首次适配（first-fit）策略，比较暴力，但无需在块内存储额外prev,succ指针，内存占用少
 * @param size size_t，待分配内存块大小
 * @param seg int，待分配内存块大小类索引
 * @return void*，返回合适空闲块地址
*/
static void *find_fit(size_t size, int seg) {
    while(seg < SEG_LEN) {
        char *root = segregated_listp + seg * WSIZE;
        char *bp = (char*)SUCC_BLKP(root);
        while(bp) {
            if((size_t)CUR_SIZE(bp) >= size) return bp;
            bp = (char*)SUCC_BLKP(bp);
        }
        seg++;
    }
    return NULL;
}

/**
 * @brief
 * 分配空闲块
 * @param bp char*，待分配空闲块地址
 * @param asize size_t，待分配空闲块大小
 * @return void*，返回分配空闲块地址
*/
static void *place(char *bp, size_t asize) {
    size_t bsize = CUR_SIZE(bp); // 获取当前空闲块大小
    size_t rm_size = bsize - asize; // 计算剩余空闲块大小
    if(!GET_ALLOC(HDRP(bp))) delete_free_block(bp); // 若当前空闲块未分配，从链表中删除
    if(rm_size >= 8 * DSIZE) { // 剩余空闲块足够大
        if(asize > 8 * DSIZE) { // 分割空闲块
            PUT(HDRP(bp), PACK(rm_size, FREE));
            PUT(FTRP(bp), PACK(rm_size, FREE));
            PUT(HDRP(NEXT_BLKP(bp)), PACK(asize, ALLOCATED));
            PUT(FTRP(NEXT_BLKP(bp)), PACK(asize, ALLOCATED));
            insert_free_block(bp);
            return NEXT_BLKP(bp);
        } else { // 不分割空闲块
            PUT(HDRP(bp), PACK(asize, ALLOCATED));
            PUT(FTRP(bp), PACK(asize, ALLOCATED));
            PUT(HDRP(NEXT_BLKP(bp)), PACK(rm_size, FREE));
            PUT(FTRP(NEXT_BLKP(bp)), PACK(rm_size, FREE));
            coalesce(NEXT_BLKP(bp));
        }
    } else { // 剩余空闲块不足
        PUT(HDRP(bp), PACK(bsize, ALLOCATED));
        PUT(FTRP(bp), PACK(bsize, ALLOCATED));
    }
    return bp;
}
/**
 * @brief
 * 初始化堆
 * @return int，返回0表示成功，-1表示失败
*/
int mm_init(void) {
    if((heap_listp = mem_sbrk((SEG_LEN + 3) * WSIZE)) == (void*)-1) return -1;
  
    // 初始化空闲块大小类头指针    
    int i;
    for(i = 0; i < SEG_LEN; ++i) PUT(heap_listp + i * WSIZE, NULL); 
    
    // 分配块
    PUT(heap_listp + (i + 0) * WSIZE, PACK(DSIZE, ALLOCATED)); // 序言块header
    PUT(heap_listp + (i + 1) * WSIZE, PACK(DSIZE, ALLOCATED)); // 序言块footer
    PUT(heap_listp + (i + 2) * WSIZE, PACK(0, ALLOCATED)); // 结尾块header，注意结尾块大小为0，没有footer，只用作哨兵

    segregated_listp = heap_listp; // 初始化分类大小类头指针
    heap_listp += (i + 1) * WSIZE; // 初始化堆开始地址

    if (extend_heap(CHUNKSIZE) == NULL) return -1;
    return 0;
}

/**
 * @brief
 * 新分配内存块，将其插入到对应大小类的链表中
 * @param size size_t，待分配内存块大小
 * @return void*，返回分配内存块地址
*/
void *mm_malloc(size_t size) {
    size_t asize = ALIGN(size); // 对齐
    size_t extendsize; // 扩展堆大小
    char *bp;
    // 无需分配
    if(size == 0) return NULL;
    // 找到适配空间
    if((bp = find_fit(asize, get_index(asize))) != NULL) return place(bp, asize);
    // 未找到适配空间
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize)) == NULL) return NULL;
    return place(bp, asize);
}

/**
 * @brief
 * 释放内存块，将其从对应大小类的链表中删除
 * @param ptr void*，待释放内存块地址
 * @return void
*/
void mm_free(void *ptr) {
    size_t size = CUR_SIZE(ptr);
    PUT(HDRP(ptr), PACK(size, FREE)); //修改头部标记
    PUT(FTRP(ptr), PACK(size, FREE)); //修改尾部标记
    coalesce(ptr);
}

/**
 * @brief
 * 重新分配内存块，若ptr为空则直接分配，若size为0则释放
 * @param ptr void*，待重新分配内存块地址
 * @param size size_t，待重新分配内存块大小
 * @return void*，返回重新分配内存块地址
*/
void *mm_realloc(void *ptr, size_t size) {
    // ptr为空直接分配
    if(ptr == NULL) return mm_malloc(size);

    // size=0就释放
    if(size == 0) {mm_free(ptr); return NULL;}

    size_t asize = ALIGN(size), total_size = CUR_SIZE(ptr);
    char *newptr;

    if(total_size == asize) return ptr; // 无需重新分配

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t next_size = NEXT_SIZE(ptr);
    char *next_bp = NEXT_BLKP(ptr);

    if(prev_alloc && !next_alloc && (total_size + next_size >= asize)) { // 前块已分配，后块未分配，且合并后空间足够
        total_size += next_size;
        delete_free_block(next_bp);
        PUT(HDRP(ptr), PACK(total_size, ALLOCATED));
        PUT(FTRP(ptr), PACK(total_size, ALLOCATED));
        place(ptr, total_size);
    } else if(!next_size && asize > total_size) { // 后块不存在，且空间不足
        size_t extend_size = asize - total_size;
        if((long)(mem_sbrk(extend_size)) == -1) return NULL;
        PUT(HDRP(ptr), PACK(total_size + extend_size, ALLOCATED));
        PUT(FTRP(ptr), PACK(total_size + extend_size, ALLOCATED));
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, ALLOCATED));
        place(ptr, asize);
    } else { // 其他情况
        if((newptr = mm_malloc(asize)) == NULL) return NULL;
        memcpy(newptr, ptr, MIN(total_size, size));
        mm_free(ptr);
        return newptr;
    }
    return ptr;
}

/********* 附录：部分测试数据生成方法 *********/
/*
1. short{1,2}-bal.rep
Tiny synthetic tracefiles for debugging

2. {amptjp,cccp,cp-decl,expr}-bal.rep
Traces generated from real programs.

3. {binary,binary2}-bal.rep
The allocation pattern is to alternatively allocate a small-sized
chunk of memory and a large-sized chunk. The small-sized chunks
(either 16 or 64 ) are deliberately set to be power of 2 while the
large-size chunks (either 112 or 448) are not a power of 2. Defeats
buddy algorithms. However, a simple-minded algorithm might prevail in
this scenario because a first-fit scheme will be good enough.

4. coalescing-bal.rep
Repeatedly allocate two equal-sized chunks (4095 in size) and release
them, and then immediately allocate and free a chunk twice as big
(8190). This tests if the students' algorithm ever really releases
memory and does coalescing. The size is chosen to give advantage to
tree-based or segrated fits algorithms where there is no header or
footer overhead.

5. {random,random2}-bal.rep	
Random allocate and free requesets that simply test the correctness
and robustness of the algorithm.

6. {realloc,realloc2}-bal.rep	
Reallocate previously allocated blocks interleaved by other allocation
request. The purpose is to test whether a certain amount of internal
fragments are allocated or not. Naive realloc implementations that
always realloc a brand new block will suffer.
*/