import struct,zlib
pal={0:(255,255,255),1:(255,0,0),2:(0,160,0),3:(0,0,255),4:(255,200,0),5:(0,0,0)}
def png(rows,fn,scale=1):
    h=len(rows); w=len(rows[0])
    data=b''
    for r in rows:
        line=bytearray()
        for v in r:
            line+=bytes(pal[v])*scale
        data+=(b'\x00'+bytes(line))*scale
    def chunk(t,d):
        return struct.pack('>I',len(d))+t+d+struct.pack('>I',zlib.crc32(t+d)&0xffffffff)
    out=b'\x89PNG\r\n\x1a\n'+chunk(b'IHDR',struct.pack('>IIBBBBB',w*scale,h*scale,8,2,0,0,0))+chunk(b'IDAT',zlib.compress(data))+chunk(b'IEND',b'')
    open(fn,'wb').write(out)
