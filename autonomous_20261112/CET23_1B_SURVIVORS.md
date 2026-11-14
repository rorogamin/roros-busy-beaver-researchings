# CET(2,3) slow survivors at 1e9 steps

Fixed Agent 1:

    1RB0RA2LB_2LA2RB1LB

Three Agent-2 tables were the `slow_same` survivors of a 20,000-trial random
search at a 500,000-step cap.  Each was then run on a blank tape from the
standard CET start (A1 at 0, A2 at 2) for 1,000,000,000 steps with
`cet23_test.exe`:

    2RB2LB0LA_1LB0RB0RB   no halt at 1e9
    1RB1RB1RA_1LB0RB0RB   no halt at 1e9
    2RB2LA2LA_1LB0RB0RB   no halt at 1e9

At the 500,000-step snapshot all three had Agent 2 moving left at about 0.034
cells/step and Agent 1 moving right, so they are slow encounters rather than
new high halting champions.  They are recorded as survivors, not champions;
no non-halting proof is claimed.
