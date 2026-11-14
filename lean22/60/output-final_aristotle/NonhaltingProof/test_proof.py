#!/usr/bin/env python3
"""Reproducible finite tests of the symbolic proof construction."""
import json
from pathlib import Path
import time
from proof import *

def main():
    root=Path(__file__).resolve().parent
    start=time.monotonic();result={'machine':MACHINE,'ranks':[],'parameter_checks':0}
    known=['ab','bcbabab','abaaacabcbacbabbcbabab']
    for r,P in enumerate(known,1):
        require(prefix(r)==P,f'Known prefix mismatch at rank {r}')
    for r in range(1,8):
        a=verify(echo(r)); b=verify(triangle(r))
        result['ranks'].append({'rank':r,'prefix_length':len(prefix(r)),
                              'prefix':prefix(r),'echo':a,'triangle':b})
        print(f'Rank {r}: echo width {a["width"]}, triangle width {b["width"]}',flush=True)
        (root/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    for r in range(1,6):
        for m in [0,1,3]:
            for q in [0,1,3]:
                for k in [0,1,4]:
                    verify(reset(r,m,q,k));verify(triangle(r,m,q,k))
                    result['parameter_checks']+=2
    # The independent checker must reject deliberately invalid histories.
    rect=triangle(3)
    mutations=[]
    for col in [0,rect.width//2,rect.width]:
        bs=list(rect.boundary)
        bs[col]='b'+bs[col][1:] if bs[col][0]!='b' else 'c'+bs[col][1:]
        mutations.append(Rectangle(rect.top,rect.bottom,tuple(bs)))
    rejected=0
    for bad in mutations:
        try:
            verify(bad)
        except InvalidCertificate:
            rejected+=1
    require(rejected==len(mutations),'A corrupted certificate was accepted')
    result['mutation_tests_rejected']=rejected
    result['elapsed_seconds']=round(time.monotonic()-start,3)
    (root/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    # A new rank beyond the original six, generated without an orbit trace.
    payload=triangle(7).payload()
    (root/'rank7_triangle.json').write_text(json.dumps(payload,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='ranks'},indent=2))

if __name__=='__main__':main()
