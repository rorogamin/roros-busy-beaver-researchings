"""Check the documented BB(3,3) claim: ID 153 and ID 758 reach the same
configuration (up to A->C->B->A, 1<->2, L<->R) at steps 1790901 / 1841608.

    ID 153: 1RB0LB0RC_2LC2LA1RA_1RA1LC---
    ID 758: 1RB2LC1RC_2LC---2RB_2LA0LB0RA

We run each machine to the claimed step count, apply the stated symmetry to
153's configuration, and compare with 758's configuration up to translation.
Both directions of the state cycle are tried, so a reversed convention in the
claim would still be detected.
"""

import bb

M153 = "1RB0LB0RC_2LC2LA1RA_1RA1LC---"
M758 = "1RB2LC1RC_2LC---2RB_2LA0LB0RA"

S153, S758 = 1790901, 1841608


def show(tag, state, tape, head, rad=10):
    tm = bb.TM(3, 3, [])
    print(f"{tag}: state={state} head={head} cells={len(tape)}")


def main():
    m153 = bb.TM.parse(M153)
    m758 = bb.TM.parse(M758)
    r153 = m153.run(S153)
    r758 = m758.run(S758)
    print(f"153 after {r153.steps}: halted={r153.halted} state={r153.state} "
          f"head={r153.head} cells={len(r153.tape)} score={r153.score()}")
    print(f"758 after {r758.steps}: halted={r758.halted} state={r758.state} "
          f"head={r758.head} cells={len(r758.tape)} score={r758.score()}")

    target = (r758.state, r758.tape, r758.head)

    for name, sm in (("A->C->B->A", {0: 2, 2: 1, 1: 0}),
                     ("inverse A->B->C->A", {0: 1, 1: 2, 2: 0})):
        for mirror in (True, False):
            c = bb.transform_config(r153.state, r153.tape, r153.head,
                                    sm, {0: 0, 1: 2, 2: 1}, mirror)
            ok = bb.same_config_up_to_translation(c, target)
            print(f"  {name:22s} mirror={mirror!s:5s} -> match={ok}")
            if ok:
                print("    VERIFIED at the documented steps")
                n1 = bb.normalize_config(c[1], c[2])
                n2 = bb.normalize_config(target[1], target[2])
                print(f"    normalized length {len(n1[1])}, head offset {n1[0]} / {n2[0]}")
                print("    758 window:", m758.rle(r758.tape, r758.head, radius=12))
                return True
    # diagnostics: compare normalized tapes at the raw step counts
    print("no match; comparing raw normalized tapes")
    print("  153 window:", m153.rle(r153.tape, r153.head, radius=12))
    print("  758 window:", m758.rle(r758.tape, r758.head, radius=12))
    return False


if __name__ == "__main__":
    main()
