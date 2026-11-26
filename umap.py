def ustep(u,d):
    # left
    if 6*d <= 2*u-12 and d%4==0: return 'bb',u+5,(9*d+20)//4
    if 6*d <= 2*u-19 and d%4==1: return 'cc',u+9,(9*d+35)//4
    if 6*d <= 2*u-12 and d%4==2: return 'bc',u+7,(9*d+26)//4
    if 6*d <= 2*u-17 and d%4==3: return 'cb',u+7,(9*d+29)//4
    if (u-1)//3 <= d <= (u-1)//2 and (u%2==1): return 'j',u+2,3*d-u+1
    return None
def run(a,c,cap=20000):
    # require c odd, a odd? U applies after state odd c; use d
    if c%2==0: return None
    d=(c-1)//2; u=(a+2*c-1)//2
    seq=[]
    for n in range(cap):
        r=ustep(u,d)
        if r is None: return seq,(u,d)
        seq.append(r); _,u,d=r
    return seq,(u,d)
for k,c in [(289,2047),(292,3),(292,2047),(37,128),(100,1)]:
    a=2*3**k-1
    seq,end=run(a,c)
    if seq is None: print(k,c,'even c'); continue
    runs=[]
    for r,u,d in seq:
        typ='L' if r!='j' else 'J'
        if runs and runs[-1][0]==typ: runs[-1][1]+=1
        else: runs.append([typ,1,r])
    print('k,c',k,c,'Usteps',len(seq),'runs',runs,'end d/u',end[1]/end[0] if end[0] else None)
