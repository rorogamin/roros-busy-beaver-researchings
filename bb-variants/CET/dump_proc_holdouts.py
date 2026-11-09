import os, sys

pid = 1688

def is_valid_tr(w, m, n):
    return (w in (0, 1)) and (m in (1, -1, 255)) and (n in (0, 1, 2))

def parse_mach2(b):
    if len(b) < 72: return None
    transitions = []
    idx = 0
    for a in range(2):
        for q in range(4):
            for b_sym in range(3):
                w = b[idx]
                m = b[idx+1]
                n = b[idx+2]
                idx += 3
                if q < 3 and b_sym < 2:
                    if not is_valid_tr(w, m, n):
                        return None
                    move_dir = 'R' if (m == 1) else 'L'
                    next_st = chr(ord('A') + n)
                    transitions.append(f"{w}{move_dir}{next_st}")
    ag0 = [ "".join(transitions[q*2 : (q+1)*2]) for q in range(3) ]
    ag1 = [ "".join(transitions[6 + q*2 : 6 + (q+1)*2]) for q in range(3) ]
    return f"{'_'.join(ag0)}|{'_'.join(ag1)}"

maps = []
with open(f"/proc/{pid}/maps") as f:
    for line in f:
        parts = line.split()
        perms = parts[1]
        if "rw" in perms and "libc" not in line and "libm" not in line and "libstdc" not in line:
            addrs = parts[0].split('-')
            start = int(addrs[0], 16)
            end = int(addrs[1], 16)
            maps.append((start, end, line.strip()))

print(f"Scanning {len(maps)} writable regions in PID {pid} (loose check)...", flush=True)

best_run = []
with open(f"/proc/{pid}/mem", "rb") as mem:
    for start, end, desc in maps:
        sz = end - start
        if sz > 100 * 1024 * 1024: continue
        try:
            mem.seek(start)
            data = mem.read(sz)
        except Exception:
            continue
        
        # Scan for contiguous run of Mach2
        offset = 0
        while offset <= len(data) - 72 * 10:
            m_first = parse_mach2(data[offset : offset + 72])
            if m_first:
                cur = offset
                run = []
                while cur + 72 <= len(data):
                    m_str = parse_mach2(data[cur : cur + 72])
                    if m_str:
                        run.append(m_str)
                        cur += 72
                    else:
                        break
                if len(run) >= 30:
                    print(f"Found {len(run)} holdouts in region 0x{start:x}!", flush=True)
                    if len(run) > len(best_run):
                        best_run = run
                    offset = cur
                else:
                    offset += 8
            else:
                offset += 8

print(f"\n=======================================================", flush=True)
print(f"TOTAL HOLDOUTS EXTRACTED: {len(best_run)}", flush=True)
print(f"=======================================================", flush=True)

if best_run:
    with open("/mnt/c/Users/Rowan/Documents/catch em/holdouts_cet3_extracted.txt", "w") as out:
        for idx, m_str in enumerate(best_run):
            out.write(f"{idx+1}\t{m_str}\n")
    print("Successfully written to holdouts_cet3_extracted.txt!", flush=True)
    print("\nFirst 10 Holdouts:", flush=True)
    for idx, m in enumerate(best_run[:10]):
        print(f"  [{idx+1}] {m}", flush=True)
    print(f"\nLast 5 Holdouts:", flush=True)
    for idx, m in enumerate(best_run[-5:]):
        print(f"  [{len(best_run)-4+idx}] {m}", flush=True)
