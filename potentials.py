from trace_ratio import trace
A=1545512812055393272156186978973263063630360047026903492257618701737754488390986882010987554468198065880319558791263685445573594052009864965
for (a,c) in [(A,2047),(706,31),(11,12)]:
    n,rs,st,end=trace(a,c)
    vals=[(a+c,min(a,c),max(a,c),a+2*c) for a,c in st]
    print('T',n,'start S,m,M,Q',vals[0],'end',vals[-1])
    # print every ~n/20 step S,m,M
    for i in range(0,len(st),max(1,len(st)//15)):
        print(i,rs[i],st[i][0].bit_length(),st[i][1].bit_length(),'S',vals[i][0].bit_length() if vals[i][0]>1000 else vals[i][0],'m',vals[i][1].bit_length() if vals[i][1]>1000 else vals[i][1])
    print()
