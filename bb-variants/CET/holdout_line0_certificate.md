# Solved CET(4) holdout: line 0 is a two-step right-running glider

Machine (line 0 of `all_holdouts_cet4.txt`):

    A1 = 1RA0LD_0LA0RA_0RD0RB_1LD0LB
    A2 = 0RD1LB_0RD1LA_1LB1RB_0RD1RC

Start: Agent 1 in A at cell 0, Agent 2 in A at cell 2, blank tape.

## Transient

After two steps:

    t = 2, p1 = 2, p2 = 4, s1 = A, s2 = D
    cells 0,1 = 1,1; cells 2,3 = 0,0; every other cell is 0.

After two more steps:

    t = 4, p1 = 4, p2 = 6, s1 = A, s2 = D
    cells 0..3 = 1,1,1,1; cells 4,5 = 0,0.

In the head-relative window `p1-2 .. p1+2`:

    t=2: 0..4 = 1,1,0,0,0
    t=4: 2..6 = 1,1,0,0,0

and the same window relative to p2 is shifted by 2 with the same values.

## Cycle

Every two steps both heads move right by two cells, the states return to
`(A,D)`, the local window around each head repeats, and the only global change
is that the two cells just vacated behind Agent 1 are filled with 1.  All cells
behind Agent 1 are 1 and all cells more than two ahead of Agent 2 are 0.

Therefore the local transition repeats forever: the pair is a right-running
glider at speed 1, the distance `p2-p1 = 2` is constant, and the agents never
collide.  This holdout is **non-halting**.

This is a finite local certificate, not a Rocq theorem.  It was checked by
direct simulation for 10,000 steps.
