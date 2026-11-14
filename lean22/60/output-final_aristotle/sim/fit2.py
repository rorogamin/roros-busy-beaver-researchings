exec(open('fit.py').read().split('tests=')[0])
import itertools
print("=== f : U2,1 U4,1 R -> ?   (R = U(a,b) then tail)")
for a in (1,2,3,4):
  for b in (1,2,3,4,5,6):
    for tail in ([('U',1,1)], [('U',1,1),('U',1,1),('U',1,4),('U',1,1)]):
        t=[('U',2,1),('U',4,1),('U',a,b)]+tail
        r=stepW(t)
        print('  R=%s  ==> %s %s'%(fmt([('U',a,b)]+tail), r[0], fmt(r[1]) if r[0]=='OK' else r[1]))
