from _ph import trace, phases
mx = (0, None); n_over = 0; n_tot = 0
for k in list(range(1, 26)) + [50, 100, 150, 200, 250, 280, 288, 289, 290, 291, 292]:
    top = 2*3**k
    cls = list(range(1, min(top, 200))) + [top//2, top//3, top//7, top-1, top-2, 2047, 2052]
    for c0v in cls:
        if not (1 <= c0v < top): continue
        for (a, c, reg, ln, i) in phases(trace(k, c0v)):
            if reg != 'J': continue
            n_tot += 1
            if c >= 355: n_over += 1
            if c > mx[0]: mx = (c, (k, c0v, a, ln))
print("J phase starts:", n_tot, "with c >= 355:", n_over)
print("max c at J phase start:", mx)
