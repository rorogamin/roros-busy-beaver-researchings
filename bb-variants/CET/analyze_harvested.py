with open("holdouts_cet3_harvested.txt") as f:
    holdouts = [line.strip().split("\t")[1] for line in f if line.strip()]

print(f"Total holdouts harvested: {len(holdouts)}")
print(f"Unique holdouts: {len(set(holdouts))}")

# Check families / prefixes
from collections import Counter
c = Counter()
for h in holdouts:
    # ag0 state A
    ag0 = h.split('|')[0]
    c[ag0[:6]] += 1

print("\nTop Ag0 State A patterns:")
for pat, cnt in c.most_common(10):
    print(f"  {pat}: {cnt}")
