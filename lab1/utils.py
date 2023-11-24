import chardet

def f1():
    s = b'o\343\377\377\221\343\377\377\263\343\377\377\322\343\377\377\355\343\377\377\b\344\377\377#\344\377\377\n'
    fencoding = chardet.detect(s)
    print(fencoding)
    s = s.decode('IBM855')
    print(s)

def f2():
    print(0x114)

print(0x1da)