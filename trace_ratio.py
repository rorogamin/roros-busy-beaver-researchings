from sample_ratio import step
def trace(a,c,cap=20000):
    c0=c; rs=[]; states=[]
    for n in range(1,cap+1):
        a2,c2,h=step(a,c)
        # identify rule letter
        if c+1<=a and c%2==0: r='a'
        elif c+2<=a and c%4==1: r='b'
        elif c+4<=a and c%4==3: r='c'
        elif c+3==a and c%4==3: r='d'
        elif c+2==a and c%4==3: r='e'
        elif c+1==a and c%2==1: r='f'
        elif c>=a and a%2==0 and c%2==0: r='g'
        elif c>=a and a%2==0 and c%2==1: r='h'
        elif c>=a and a%2==1 and c%2==0: r='i'
        else: r='j'
        rs.append(r); states.append((a,c))
        if h or a2==1 or 2*c2<=c0:
            return n,rs,states,(a2,c2,h)
        a,c=a2,c2
    return cap,rs,states,(a,c,False)
A=1545512812055393272156186978973263063630360047026903492257618701737754488390986882010987554468198065880319558791263685445573594052009864965
for (a,c) in [(A,2047),(1,2715403),(706,31),(1610,12)]:
    n,rs,st,end=trace(a,c)
    print('start',a.bit_length() if a>1000 else a,c,'T',n,'end',end[:2])
    # run lengths
    runs=[]
    for r in rs:
        if runs and runs[-1][0]==r: runs[-1][1]+=1
        else: runs.append([r,1])
    print('runs',runs[:30], '... totalruns',len(runs))
    print('maxratio', max(st[i][0]/max(1,st[i][1]) for i in range(len(st))))
