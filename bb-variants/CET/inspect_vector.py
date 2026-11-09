import os, struct

pid = 1688

# Read seeds to get some known transition patterns
seeds = []
with open("cet3_all_seeds.txt") as f:
    for line in f:
        line = line.strip()
        if not line: continue
        parts = line.split()
        m_str = parts[-1]
        if '|' in m_str:
            seeds.append(m_str)

print(f"Loaded {len(seeds)} seeds. Top seed: {seeds[0]}")

# Convert a machine string to 72 bytes
def str_to_bytes(s):
    # s is like "0LB0LC_1RB1LA_1RC0LA|1LB0RC_1RA1LB_0LB1RC"
    # Mach2 is t[2][4][3] where each Tr is (w, m, n)
    b = bytearray(72)
    agents = s.split('|')
    for a in range(2):
        states = agents[a].split('_')
        for q in range(3):
            # Each state has 2 transitions (sym 0, sym 1)
            # tr0 is s[0:3], tr1 is s[3:6]
            st_str = states[q]
            for sym in range(2):
                w = int(st_str[sym*3])
                m = 1 if st_str[sym*3 + 1] == 'R' else -1 # 255 in uint8
                n = ord(st_str[sym*3 + 2]) - ord('A')
                idx = ((a * 4 + q) * 3 + sym) * 3
                b[idx] = w
                b[idx+1] = m & 0xFF
                b[idx+2] = n
    return bytes(b)

seed0_b = str_to_bytes(seeds[0])
print(f"Seed 0 byte length: {len(seed0_b)}, hex prefix: {seed0_b[:18].hex()}")

# Now read /proc/1688/maps
maps = []
with open(f"/proc/{pid}/maps") as f:
    for line in f:
        parts = line.split()
        perms = parts[1]
        if "rw" in perms:
            addrs = parts[0].split('-')
            start = int(addrs[0], 16)
            end = int(addrs[1], 16)
            maps.append((start, end, line.strip()))

# Look for std::vector pointers in [stack] or heap
# A std::vector<Mach2> has begin, end, cap
# end - begin must be count * 72 where count is between 800 and 900
found_vectors = []
with open(f"/proc/{pid}/mem", "rb") as mem:
    for start, end, desc in maps:
        sz = end - start
        if sz > 200 * 1024 * 1024: continue
        try:
            mem.seek(start)
            data = mem.read(sz)
        except Exception:
            continue
        
        # Scan for 3 uint64 pointers
        for off in range(0, sz - 24, 8):
            p_begin, p_end, p_cap = struct.unpack_from("<QQQ", data, off)
            if p_begin > 0x10000 and p_end > p_begin and p_cap >= p_end:
                byte_len = p_end - p_begin
                if byte_len % 72 == 0:
                    cnt = byte_len // 72
                    if 700 <= cnt <= 1200:
                        found_vectors.append((p_begin, p_end, p_cap, cnt, desc))

print(f"Found {len(found_vectors)} matching std::vector<Mach2> structures:")
for v in found_vectors:
    print(f"  count={v[3]}, begin=0x{v[0]:x}, end=0x{v[1]:x}, desc={v[4]}")

if found_vectors:
    # Read the elements from the vector
    p_begin, p_end, p_cap, cnt, _ = found_vectors[0]
    with open(f"/proc/{pid}/mem", "rb") as mem:
        mem.seek(p_begin)
        vec_bytes = mem.read(cnt * 72)
    
    # Parse each Mach2
    def bytes_to_str(b):
        parts = []
        for a in range(2):
            states = []
            for q in range(3):
                tr_strs = []
                for sym in range(2):
                    idx = ((a * 4 + q) * 3 + sym) * 3
                    w = b[idx]
                    m = 'R' if b[idx+1] == 1 else 'L'
                    n = chr(ord('A') + b[idx+2])
                    tr_strs.append(f"{w}{m}{n}")
                states.append("".join(tr_strs))
            parts.append("_".join(states))
        return "|".join(parts)
    
    extracted = []
    for i in range(cnt):
        m_b = vec_bytes[i*72 : (i+1)*72]
        extracted.append(bytes_to_str(m_b))
    
    with open("holdouts_cet3_harvested.txt", "w") as out:
        for idx, m in enumerate(extracted):
            out.write(f"{idx+1}\t{m}\n")
    print(f"\nSuccessfully wrote {cnt} holdouts to holdouts_cet3_harvested.txt!")
    print("\nFirst 10 holdouts:")
    for i, m in enumerate(extracted[:10]):
        print(f"  [{i+1}] {m}")
    print("\nLast 5 holdouts:")
    for i, m in enumerate(extracted[-5:]):
        print(f"  [{cnt - 5 + i + 1}] {m}")
