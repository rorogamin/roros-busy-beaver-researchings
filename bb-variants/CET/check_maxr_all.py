lines = open("C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/eval_towers.py").read().splitlines()
ns = {}; exec("\n".join(lines[:401]), ns)
parse_mech_line = ns["parse_mech_line"]
exact_tower_rounds = ns["exact_tower_rounds"]

# Upper bound check on (events): can ANY initial (G in B, L2) reach >= target_r rounds?
# Notice exact_tower_rounds isn't needed if we just check B graph? Actually wait:
# in exact_tower_rounds, L_n quickly explodes (1 tower step -> L huge), so only G transitions matter modulo Carmichael/cycle!
# Let's check for EVERY line what max rounds ANY (G, L0 in 10..40) or cycle+tail gives!
# Even simpler: compute max length of B* H walk where G' transitions match, OR sample L0 in small set?
# Wait: why guess L0?! Find if there is a path in (B + H) graph starting at some G, OR remember find_multiround_candidates:
# In exact_tower_rounds, B events deterministically produce next gap ONLY depending on mod residues!
# So let's just check ALL unique (events_str) in mechs_*.txt and test which ones can EVER reach >= target_r!

def can_reach_maxr(m, target_r):
    B = m["events"]
    # Wait: just test graph reachability ignoring exact residue, i.e. any G -> any reachable G?
    # Better: run exact_tower_rounds across G in B and L in range(8, 30)! Wait: at R>=2, (xr, ts, lp, w, ... ) might give L2 mod M,
    # Wait why did deep_cet3.txt ALREADY compute MAXR?! Let's check how deep_cet3.txt computed MAXR!!
    # Look: earlier inspect_big_r1 read MAXR from r1_exact_cet3.txt, which got MAXR from check_multiround or whatever built deep_cet3.txt!
    return True

for name, mpath, outpath, minr in [
    ("CET3", "mechs_cet3.txt", "all_pot5_cet3.txt", 5),
    ("CET23_t1", "mechs_cet23_t1.txt", "all_pot9_cet23_t1.txt", 9),
    ("CET23_t2", "mechs_cet23_t2.txt", "all_pot9_cet23_t2.txt", 9),
]:
    full = "C:/Users/Rowan/Documents/st/bbwork/bb-variants/CET/"
    # Check unique event signatures first so we test modularity FAST!
    rows = open(full + mpath).read().splitlines()
    # Extract events substring (after |B: or |H:) and compute upper-bound MAXR via exact mod search just like deep_cet did!
    # Wait let's test across L2 mod period? Even faster: read deep_*.txt to see WHICH unique event sigs hit MAXR >= minr!!
    pass
