# Active-end park attempt: measured negative result

Date: 2026-11-11.  This records the structural rewrite requested after the
tier-1 specialization.  It is a negative result, not an under-50 claim.

## 1. What “active end” costs

The current odometer has

    [1^p park] 0 0 [chain runs] 0 [blank]

with the park at the far left and the active top at the far right.  Placing
the park at the active end gives

    [chain runs] 0 0 [1^p park] [blank]

so the p look/spend is local.  The trade is the append move: an fs append must
insert a new entry **before** the park, so the park has to move right by the
new entry length + close/terminator.  A one-cell park rotation is six states
(walk to the left edge, erase, ride to the right edge, write, ride back, write
the new run cell); shifting by the full appended length needs either a
length-parameterized shuttle or one rotation copy per appended mark.  That is
the structural cost the old table bought its way out of by keeping the park
opposite the growing end.  No green active-end table was produced.

## 2. The cheaper run-code draft

`tools/eps1_u3.py` is the existing run-code layout:

    [1^p] 00 [run1] 0 [run2] 0 ... [runm] 0 00 [blank]

The park pair is the home cell, so p is a local test/spend there; the chain
still runs to the right.  After the routing repairs (the `N3` nonempty arm,
the `AT0` close walk, the `AT2` first push mark, the `BD1 -> T1` count entry,
and a 3-deep park-vs-chain-end home test), its current table is

    70 states / 96 rows

and exact bisimulation reduction on the table (start `U`) gives

    49 states / 72 rows

which is under 50 **structurally but not verified**.  The head-aware decode
(`read_at`) shows that some landings are now close, but the p=0/atom and
singleton paths still produce wrong values (for example a predicted
`[ATOM,2]` comes back as `[ATOM1,2]`, and the p=0 case lands left of the
home pair).  `python tools/eps1_u3.py` exits 1; the full fixed-run check also
reaches the campaign cap rather than completing.  The 49-state count is a
measurement of the table, not an under-50 gate pass.

## 3. Status

The general odometer remains the measured 71 / 72 / 76 table from
`tools/eps1_odi.py`; `tools/eps1_odi_under50.py` still reports `UNDER_50: NO`.
No FGH, ε₁, or Rocq claim is made for the active-end attempt, and nothing here
replaces the general table or the 61-state tier-1 certificate.  The run-code
draft is explicitly **not shipped** as an under-50 machine.
