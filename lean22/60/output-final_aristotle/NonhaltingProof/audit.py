#!/usr/bin/env python3
"""Second interpreter: whole finite blocks, separately coded TM cases.

The constructive generator's intermediate boundary words are ignored here.
Only the outer words, starting tape, and claimed final tape are supplied.
"""
import hashlib
import json
from pathlib import Path
from proof import reset, triangle, verify, prefix, require, ones_wall


def step(q, s):
    # q = 0 for A and 1 for B.  Movement +1 means physically right.
    if q == 0:
        if s == 0: return 1, 1, 1
        if s == 1: return 0, 2, -1
        if s == 2: return 1, 3, -1
        if s == 3: return 1, 4, -1
        raise ValueError('A4: halting transition')
    if s == 0: return 0, 0, -1
    if s == 1: return 1, 4, -1
    if s == 2: return 0, 3, 1
    if s == 3: return 0, 4, -1
    if s == 4: return 1, 0, 1
    raise ValueError('Invalid symbol')


def decode(letter):
    if letter == 'a': return 0, 1
    if letter == 'b': return 1, 1
    if letter == 'c': return 0, 0
    raise ValueError('Invalid pair')


def whole_block(rect):
    tape=list(rect.top); j=0; steps=0
    for letter in rect.boundary[0]:
        q, expected=decode(letter); pos=0
        while pos >= 0:
            q,tape[pos],move=step(q,tape[pos]); steps+=1
            pos-=move  # Array order is right-to-left.
            if pos == len(tape):
                require(j < len(rect.boundary[-1]),'Left oracle exhausted')
                entry,ret=decode(rect.boundary[-1][j]);j+=1
                require(q==entry,'Wrong left entry')
                q=ret;pos-=1
        require(q==expected,'Wrong right return')
    require(tuple(tape)==rect.bottom,'Wrong final tape')
    require(j==len(rect.boundary[-1]),'Unused left oracle suffix')
    require(steps==verify(rect)['local_tm_steps'],'Interpreters disagree on step count')
    return steps


def right_engine(m, phase):
    u=[0,4,2]*m
    original=[u,[2]+u,[4,2]+u][phase]
    expected=[[2]+u,[4,2]+u,[0,4,2]+u][phase]
    q=[0,1,1][phase]; expected_q=[0,1,0][phase]
    tape=list(original)+[0]*8; pos=0; steps=0
    while pos >= 0:
        require(pos<len(tape),'Engine escaped available right padding')
        q,tape[pos],move=step(q,tape[pos]);pos+=move;steps+=1
        require(steps<100000,'Engine test exceeded guard')
    require(q==expected_q,'Wrong engine exit state')
    require(tape==expected+[0]*(len(tape)-len(expected)),'Wrong engine output')
    require(steps==6*m+3+2*phase,'Wrong engine duration')


def main():
    root=Path(__file__).resolve().parent
    result={'whole_block_cases':0,'whole_block_tm_steps':0,'right_engine_cases':0}
    for r in range(1,5):
        for m in [0,2]:
            for q in [0,2]:
                for k in [0,3]:
                    for builder in [reset,triangle]:
                        result['whole_block_tm_steps']+=whole_block(builder(r,m,q,k))
                        result['whole_block_cases']+=1
    for m in range(101):
        for phase in range(3):
            right_engine(m,phase);result['right_engine_cases']+=1
    result['prefix_sha256']={str(r):hashlib.sha256(prefix(r).encode()).hexdigest()
                             for r in range(1,8)}
    # These hashes audit the match to the six independently supplied earlier
    # prefixes. They are never used by the constructive generator.
    prior_hashes = [
        'fb8e20fc2e4c3f248c60c39bd652f3c1347298bb977b8b4d5903b85055620603',
        '23d5921848baf16cdae0fc371157d63c680847f1c60714df443758dc702d9328',
        'faf38f504a2cccd098b11ff1d5bebe3c2ce345d17cbae8e75f309eee946fedaa',
        '4f28a7ad8626f5e03f0d5d8cc4b31b0b45263ac5d26b83f59d06c9db84a98dd6',
        '6d5ceb41a31e7c4674229589b8729291269d8cb92770000fd4123878c5600ba3',
        '0b03f3ccf022369ed23ec123c99fc88af44028682e46d42966adff1799a145f7',
    ]
    result['matches_all_six_prior_prefixes'] = {
        str(r):result['prefix_sha256'][str(r)] == expected
        for r,expected in enumerate(prior_hashes,1)}
    require(all(result['matches_all_six_prior_prefixes'].values()),
            'An independently recorded prefix does not match')
    count=0
    for length in [1,3,5,9,101]:
        h=(length-1)//2
        for m in [1,2,5]:
            for q in [h,h+1,h+4]:
                for k in [0,1,3]:
                    verify(ones_wall(length,m,q,k));count+=1
    result['additional_wall_edge_cases']=count
    (root/'independent_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
