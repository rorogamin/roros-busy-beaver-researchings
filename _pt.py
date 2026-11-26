from _ph import trace, phases
def show(k,c0v):
    seq=trace(k,c0v); ph=phases(seq)
    print("k=%d c0=%d totlen=%d c0/2=%d"%(k,c0v,len(seq),c0v//2))
    for (a,c,reg,ln,i) in ph:
        print("  step %3d  %s len %3d  a=%d c=%d  a/c=%.2f"%(i,reg,ln,a,c,a/c if c else -1))
for (k,v) in [(289,2047),(292,1),(291,35)]:
    show(k,v); print()
