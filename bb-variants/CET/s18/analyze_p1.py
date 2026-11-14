from collections import Counter

oob = [l.strip().split('\t') for l in open('bbwork/bb-variants/CET/s18/p1_oob.txt') if l.strip()]
rem = [l.strip().split('\t') for l in open('bbwork/bb-variants/CET/s18/p1_rem.txt') if l.strip()]

print(f"OOB count: {len(oob)}")
print(f"REM count: {len(rem)}")

widths = [int(r[4]) - int(r[3]) for r in rem]
buckets = Counter()
for w in widths:
    if w < 30: buckets['<30 (tiny/log)'] += 1
    elif w < 100: buckets['30-99 (small/counter)'] += 1
    elif w < 500: buckets['100-499 (medium/bouncer)'] += 1
    elif w < 5000: buckets['500-4999 (large/bouncer)'] += 1
    else: buckets['>=5000 (huge)'] += 1

print("Width distribution in REM at 2M steps:")
for k, v in sorted(buckets.items()):
    print(f"  {k}: {v}")
