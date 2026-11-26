/-
  GENERATED FILE — do not edit.

  Emitted by proof/emit_ladder.js from ../ladder.json, in ladder order.
  `ladder.json.order` is authoritative; its `entries` array is not in
  ladder order, so enumerating `entries` directly misnumbers machines.
-/
import CET4.Basic

namespace CET4

/-- Prima agent 1 — `0LB1LB_1LC1RB_0RD0LC_1RA0LD` -/
def tPrimaA1 : Table := fun s b =>
  match s.val * 2 + (if b then 1 else 0) with
  | 0 => ⟨false, Dir.L, 1⟩
  | 1 => ⟨true, Dir.L, 1⟩
  | 2 => ⟨true, Dir.L, 2⟩
  | 3 => ⟨true, Dir.R, 1⟩
  | 4 => ⟨false, Dir.R, 3⟩
  | 5 => ⟨false, Dir.L, 2⟩
  | 6 => ⟨true, Dir.R, 0⟩
  | 7 => ⟨false, Dir.L, 3⟩
  | _ => ⟨false, Dir.R, 0⟩

/-- Prima agent 2 — `1LB1LC_1RC0RA_1RA0RD_1RB0LA` -/
def tPrimaA2 : Table := fun s b =>
  match s.val * 2 + (if b then 1 else 0) with
  | 0 => ⟨true, Dir.L, 1⟩
  | 1 => ⟨true, Dir.L, 2⟩
  | 2 => ⟨true, Dir.R, 2⟩
  | 3 => ⟨false, Dir.R, 0⟩
  | 4 => ⟨true, Dir.R, 0⟩
  | 5 => ⟨false, Dir.R, 3⟩
  | 6 => ⟨true, Dir.R, 1⟩
  | 7 => ⟨false, Dir.L, 0⟩
  | _ => ⟨false, Dir.R, 0⟩

/-- Firstal agent 1 — `1LB0LD_0LC0RC_1LD1RC_1RA0LD` -/
def tFirstalA1 : Table := fun s b =>
  match s.val * 2 + (if b then 1 else 0) with
  | 0 => ⟨true, Dir.L, 1⟩
  | 1 => ⟨false, Dir.L, 3⟩
  | 2 => ⟨false, Dir.L, 2⟩
  | 3 => ⟨false, Dir.R, 2⟩
  | 4 => ⟨true, Dir.L, 3⟩
  | 5 => ⟨true, Dir.R, 2⟩
  | 6 => ⟨true, Dir.R, 0⟩
  | 7 => ⟨false, Dir.L, 3⟩
  | _ => ⟨false, Dir.R, 0⟩

/-- Firstal agent 2 — `0RB0RD_0LC0RA_0LD1RA_1RB1LD` -/
def tFirstalA2 : Table := fun s b =>
  match s.val * 2 + (if b then 1 else 0) with
  | 0 => ⟨false, Dir.R, 1⟩
  | 1 => ⟨false, Dir.R, 3⟩
  | 2 => ⟨false, Dir.L, 2⟩
  | 3 => ⟨false, Dir.R, 0⟩
  | 4 => ⟨false, Dir.L, 3⟩
  | 5 => ⟨true, Dir.R, 0⟩
  | 6 => ⟨true, Dir.R, 1⟩
  | 7 => ⟨true, Dir.L, 3⟩
  | _ => ⟨false, Dir.R, 0⟩

/-- Dancer agent 1 — `0LB0RB_1LC1RB_1RD0LC_1LA0LC` -/
def tDancerA1 : Table := fun s b =>
  match s.val * 2 + (if b then 1 else 0) with
  | 0 => ⟨false, Dir.L, 1⟩
  | 1 => ⟨false, Dir.R, 1⟩
  | 2 => ⟨true, Dir.L, 2⟩
  | 3 => ⟨true, Dir.R, 1⟩
  | 4 => ⟨true, Dir.R, 3⟩
  | 5 => ⟨false, Dir.L, 2⟩
  | 6 => ⟨true, Dir.L, 0⟩
  | 7 => ⟨false, Dir.L, 2⟩
  | _ => ⟨false, Dir.R, 0⟩

/-- Dancer agent 2 — `0RB1RC_1LC0LB_0LD0RC_1RA1LD` -/
def tDancerA2 : Table := fun s b =>
  match s.val * 2 + (if b then 1 else 0) with
  | 0 => ⟨false, Dir.R, 1⟩
  | 1 => ⟨true, Dir.R, 2⟩
  | 2 => ⟨true, Dir.L, 2⟩
  | 3 => ⟨false, Dir.L, 1⟩
  | 4 => ⟨false, Dir.L, 3⟩
  | 5 => ⟨false, Dir.R, 2⟩
  | 6 => ⟨true, Dir.R, 0⟩
  | 7 => ⟨true, Dir.L, 3⟩
  | _ => ⟨false, Dir.R, 0⟩

/-- Cupid agent 1 — `1LB1RA_1RC0LB_1LD1RD_1RA0RC` -/
def tCupidA1 : Table := fun s b =>
  match s.val * 2 + (if b then 1 else 0) with
  | 0 => ⟨true, Dir.L, 1⟩
  | 1 => ⟨true, Dir.R, 0⟩
  | 2 => ⟨true, Dir.R, 2⟩
  | 3 => ⟨false, Dir.L, 1⟩
  | 4 => ⟨true, Dir.L, 3⟩
  | 5 => ⟨true, Dir.R, 3⟩
  | 6 => ⟨true, Dir.R, 0⟩
  | 7 => ⟨false, Dir.R, 2⟩
  | _ => ⟨false, Dir.R, 0⟩

/-- Cupid agent 2 — `0RB1LC_0RC0LC_1RD0LA_1LA1RB` -/
def tCupidA2 : Table := fun s b =>
  match s.val * 2 + (if b then 1 else 0) with
  | 0 => ⟨false, Dir.R, 1⟩
  | 1 => ⟨true, Dir.L, 2⟩
  | 2 => ⟨false, Dir.R, 2⟩
  | 3 => ⟨false, Dir.L, 2⟩
  | 4 => ⟨true, Dir.R, 3⟩
  | 5 => ⟨false, Dir.L, 0⟩
  | 6 => ⟨true, Dir.L, 0⟩
  | 7 => ⟨true, Dir.R, 1⟩
  | _ => ⟨false, Dir.R, 0⟩

/-- Celestal agent 1 — `0LB1RB_1LC1RB_1RD0LC_1LD0RA` -/
def tCelestalA1 : Table := fun s b =>
  match s.val * 2 + (if b then 1 else 0) with
  | 0 => ⟨false, Dir.L, 1⟩
  | 1 => ⟨true, Dir.R, 1⟩
  | 2 => ⟨true, Dir.L, 2⟩
  | 3 => ⟨true, Dir.R, 1⟩
  | 4 => ⟨true, Dir.R, 3⟩
  | 5 => ⟨false, Dir.L, 2⟩
  | 6 => ⟨true, Dir.L, 3⟩
  | 7 => ⟨false, Dir.R, 0⟩
  | _ => ⟨false, Dir.R, 0⟩

/-- Celestal agent 2 — `1LB0RB_1RC0LC_1RD1LD_1RA1RB` -/
def tCelestalA2 : Table := fun s b =>
  match s.val * 2 + (if b then 1 else 0) with
  | 0 => ⟨true, Dir.L, 1⟩
  | 1 => ⟨false, Dir.R, 1⟩
  | 2 => ⟨true, Dir.R, 2⟩
  | 3 => ⟨false, Dir.L, 2⟩
  | 4 => ⟨true, Dir.R, 3⟩
  | 5 => ⟨true, Dir.L, 3⟩
  | 6 => ⟨true, Dir.R, 0⟩
  | 7 => ⟨true, Dir.R, 1⟩
  | _ => ⟨false, Dir.R, 0⟩

/-- Rudolph agent 1 — `0LB1LB_1LC1RB_1RA0LD_0RC0LD` -/
def tRudolphA1 : Table := fun s b =>
  match s.val * 2 + (if b then 1 else 0) with
  | 0 => ⟨false, Dir.L, 1⟩
  | 1 => ⟨true, Dir.L, 1⟩
  | 2 => ⟨true, Dir.L, 2⟩
  | 3 => ⟨true, Dir.R, 1⟩
  | 4 => ⟨true, Dir.R, 0⟩
  | 5 => ⟨false, Dir.L, 3⟩
  | 6 => ⟨false, Dir.R, 2⟩
  | 7 => ⟨false, Dir.L, 3⟩
  | _ => ⟨false, Dir.R, 0⟩

/-- Rudolph agent 2 — `1RB1RD_0RC0LA_1LA1RA_0LD1LB` -/
def tRudolphA2 : Table := fun s b =>
  match s.val * 2 + (if b then 1 else 0) with
  | 0 => ⟨true, Dir.R, 1⟩
  | 1 => ⟨true, Dir.R, 3⟩
  | 2 => ⟨false, Dir.R, 2⟩
  | 3 => ⟨false, Dir.L, 0⟩
  | 4 => ⟨true, Dir.L, 0⟩
  | 5 => ⟨true, Dir.R, 0⟩
  | 6 => ⟨false, Dir.L, 3⟩
  | 7 => ⟨true, Dir.L, 1⟩
  | _ => ⟨false, Dir.R, 0⟩

/-- Trimestrius agent 1 — `0LB0LC_1RA1RC_0RD0LC_1LA1RD` -/
def tTrimestriusA1 : Table := fun s b =>
  match s.val * 2 + (if b then 1 else 0) with
  | 0 => ⟨false, Dir.L, 1⟩
  | 1 => ⟨false, Dir.L, 2⟩
  | 2 => ⟨true, Dir.R, 0⟩
  | 3 => ⟨true, Dir.R, 2⟩
  | 4 => ⟨false, Dir.R, 3⟩
  | 5 => ⟨false, Dir.L, 2⟩
  | 6 => ⟨true, Dir.L, 0⟩
  | 7 => ⟨true, Dir.R, 3⟩
  | _ => ⟨false, Dir.R, 0⟩

/-- Trimestrius agent 2 — `0RB1LD_1RC0RC_1LC0RA_1RA0LD` -/
def tTrimestriusA2 : Table := fun s b =>
  match s.val * 2 + (if b then 1 else 0) with
  | 0 => ⟨false, Dir.R, 1⟩
  | 1 => ⟨true, Dir.L, 3⟩
  | 2 => ⟨true, Dir.R, 2⟩
  | 3 => ⟨false, Dir.R, 2⟩
  | 4 => ⟨true, Dir.L, 2⟩
  | 5 => ⟨false, Dir.R, 0⟩
  | 6 => ⟨true, Dir.R, 0⟩
  | 7 => ⟨false, Dir.L, 3⟩
  | _ => ⟨false, Dir.R, 0⟩

/-- Quadrestrius agent 1 — `0LB0RD_1LC1RB_1RD0LC_1LA1RB` -/
def tQuadrestriusA1 : Table := fun s b =>
  match s.val * 2 + (if b then 1 else 0) with
  | 0 => ⟨false, Dir.L, 1⟩
  | 1 => ⟨false, Dir.R, 3⟩
  | 2 => ⟨true, Dir.L, 2⟩
  | 3 => ⟨true, Dir.R, 1⟩
  | 4 => ⟨true, Dir.R, 3⟩
  | 5 => ⟨false, Dir.L, 2⟩
  | 6 => ⟨true, Dir.L, 0⟩
  | 7 => ⟨true, Dir.R, 1⟩
  | _ => ⟨false, Dir.R, 0⟩

/-- Quadrestrius agent 2 — `1LB0RC_1RA0RD_1LA1RB_1LD1LC` -/
def tQuadrestriusA2 : Table := fun s b =>
  match s.val * 2 + (if b then 1 else 0) with
  | 0 => ⟨true, Dir.L, 1⟩
  | 1 => ⟨false, Dir.R, 2⟩
  | 2 => ⟨true, Dir.R, 0⟩
  | 3 => ⟨false, Dir.R, 3⟩
  | 4 => ⟨true, Dir.L, 0⟩
  | 5 => ⟨true, Dir.R, 1⟩
  | 6 => ⟨true, Dir.L, 3⟩
  | 7 => ⟨true, Dir.L, 2⟩
  | _ => ⟨false, Dir.R, 0⟩

/-- Dasher agent 1 — `1LB0LC_1LC1RB_1RA0LD_0RC0LD` -/
def tDasherA1 : Table := fun s b =>
  match s.val * 2 + (if b then 1 else 0) with
  | 0 => ⟨true, Dir.L, 1⟩
  | 1 => ⟨false, Dir.L, 2⟩
  | 2 => ⟨true, Dir.L, 2⟩
  | 3 => ⟨true, Dir.R, 1⟩
  | 4 => ⟨true, Dir.R, 0⟩
  | 5 => ⟨false, Dir.L, 3⟩
  | 6 => ⟨false, Dir.R, 2⟩
  | 7 => ⟨false, Dir.L, 3⟩
  | _ => ⟨false, Dir.R, 0⟩

/-- Dasher agent 2 — `0RB0LB_1RC0LD_1LD1RA_0RA1LB` -/
def tDasherA2 : Table := fun s b =>
  match s.val * 2 + (if b then 1 else 0) with
  | 0 => ⟨false, Dir.R, 1⟩
  | 1 => ⟨false, Dir.L, 1⟩
  | 2 => ⟨true, Dir.R, 2⟩
  | 3 => ⟨false, Dir.L, 3⟩
  | 4 => ⟨true, Dir.L, 3⟩
  | 5 => ⟨true, Dir.R, 0⟩
  | 6 => ⟨false, Dir.R, 0⟩
  | 7 => ⟨true, Dir.L, 1⟩
  | _ => ⟨false, Dir.R, 0⟩

/-- Vixen agent 1 — `1LB1RA_1RC0LB_0LD1RD_1RA0RD` -/
def tVixenA1 : Table := fun s b =>
  match s.val * 2 + (if b then 1 else 0) with
  | 0 => ⟨true, Dir.L, 1⟩
  | 1 => ⟨true, Dir.R, 0⟩
  | 2 => ⟨true, Dir.R, 2⟩
  | 3 => ⟨false, Dir.L, 1⟩
  | 4 => ⟨false, Dir.L, 3⟩
  | 5 => ⟨true, Dir.R, 3⟩
  | 6 => ⟨true, Dir.R, 0⟩
  | 7 => ⟨false, Dir.R, 3⟩
  | _ => ⟨false, Dir.R, 0⟩

/-- Vixen agent 2 — `0RB1LC_1RD0RD_1RA0LC_1LD0RA` -/
def tVixenA2 : Table := fun s b =>
  match s.val * 2 + (if b then 1 else 0) with
  | 0 => ⟨false, Dir.R, 1⟩
  | 1 => ⟨true, Dir.L, 2⟩
  | 2 => ⟨true, Dir.R, 3⟩
  | 3 => ⟨false, Dir.R, 3⟩
  | 4 => ⟨true, Dir.R, 0⟩
  | 5 => ⟨false, Dir.L, 2⟩
  | 6 => ⟨true, Dir.L, 3⟩
  | 7 => ⟨false, Dir.R, 0⟩
  | _ => ⟨false, Dir.R, 0⟩

/-- Comet agent 1 — `1LB1RA_0RC0LB_1RD1LC_1RA1LD` -/
def tCometA1 : Table := fun s b =>
  match s.val * 2 + (if b then 1 else 0) with
  | 0 => ⟨true, Dir.L, 1⟩
  | 1 => ⟨true, Dir.R, 0⟩
  | 2 => ⟨false, Dir.R, 2⟩
  | 3 => ⟨false, Dir.L, 1⟩
  | 4 => ⟨true, Dir.R, 3⟩
  | 5 => ⟨true, Dir.L, 2⟩
  | 6 => ⟨true, Dir.R, 0⟩
  | 7 => ⟨true, Dir.L, 3⟩
  | _ => ⟨false, Dir.R, 0⟩

/-- Comet agent 2 — `1RB0RB_1LB0RC_0RA1LD_1RC0LD` -/
def tCometA2 : Table := fun s b =>
  match s.val * 2 + (if b then 1 else 0) with
  | 0 => ⟨true, Dir.R, 1⟩
  | 1 => ⟨false, Dir.R, 1⟩
  | 2 => ⟨true, Dir.L, 1⟩
  | 3 => ⟨false, Dir.R, 2⟩
  | 4 => ⟨false, Dir.R, 0⟩
  | 5 => ⟨true, Dir.L, 3⟩
  | 6 => ⟨true, Dir.R, 2⟩
  | 7 => ⟨false, Dir.L, 3⟩
  | _ => ⟨false, Dir.R, 0⟩

/-- The ladder, in order 1..11. -/
def Ladder : List Pair := [
  ⟨"Prima", tPrimaA1, tPrimaA2⟩,
  ⟨"Firstal", tFirstalA1, tFirstalA2⟩,
  ⟨"Dancer", tDancerA1, tDancerA2⟩,
  ⟨"Cupid", tCupidA1, tCupidA2⟩,
  ⟨"Celestal", tCelestalA1, tCelestalA2⟩,
  ⟨"Rudolph", tRudolphA1, tRudolphA2⟩,
  ⟨"Trimestrius", tTrimestriusA1, tTrimestriusA2⟩,
  ⟨"Quadrestrius", tQuadrestriusA1, tQuadrestriusA2⟩,
  ⟨"Dasher", tDasherA1, tDasherA2⟩,
  ⟨"Vixen", tVixenA1, tVixenA2⟩,
  ⟨"Comet", tCometA1, tCometA2⟩
]

/-- The claimed tower height, as recorded in ladder.json (model output). -/
def ClaimedR : List (String × Nat) := [
  ("Prima", 16),
  ("Firstal", 17),
  ("Dancer", 18),
  ("Cupid", 19),
  ("Celestal", 20),
  ("Rudolph", 21),
  ("Trimestrius", 22),
  ("Quadrestrius", 24),
  ("Dasher", 25),
  ("Vixen", 25),
  ("Comet", 25)
]

end CET4
