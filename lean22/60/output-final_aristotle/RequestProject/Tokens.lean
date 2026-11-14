import RequestProject.Local

/-!
# The token alphabet of the tape

Simulation shows that at every moment at which the head of
`1RB2LA3LB4LB---_0LA4LB3RA4LA0RB` reaches a **new leftmost cell in state `B`** (these
moments recur every three cells of leftward growth), the non-blank part of the tape is a
concatenation of just two kinds of word:

* `tokU a b = 0 4^a 2^b`   (`a ≥ 1`, `b ≥ 1`), and
* `tokV c   = 4 3 2^c`     (`c ≥ 0`),

with no two `tokV` adjacent, the first token a `tokU`, the last token a `tokU a 1`, and
every `tokV` preceded by a `tokU a b` with `b ≥ 2`.  This file fixes the notation; the
macro rules that move the machine from one such configuration to the next are in
`LeftRules.lean`.

The reason this alphabet is the right one is the shape of the *rightward* moves of the
machine: `A:0 → 1RB`, `B:2 → 3RA` and `B:4 → 0RB`.  A rightward excursion started in
state `A` on a `0` therefore reads exactly `0 4^{a} 2`, rewrites it as `1 0^{a} 3`, and
comes back to state `A` — so it runs through the tokens with `b = 1` and is turned around
by the first token with `b ≥ 2`.
-/

namespace BB25

/-- The token `0 4^a 2^b`. -/
def tokU (a b : ℕ) : List Sym := 0 :: (List.replicate a 4 ++ List.replicate b 2)

/-- The token `4 3 2^c`. -/
def tokV (c : ℕ) : List Sym := 4 :: 3 :: List.replicate c 2

@[simp] lemma tokU_length (a b : ℕ) : (tokU a b).length = 1 + a + b := by
  simp [tokU]; omega

@[simp] lemma tokV_length (c : ℕ) : (tokV c).length = 2 + c := by
  simp [tokV]; omega

lemma tokU_zero_zero : tokU 0 0 = [0] := rfl
lemma tokU_two_one : tokU 2 1 = [0, 4, 4, 2] := rfl
lemma tokU_two_two : tokU 2 2 = [0, 4, 4, 2, 2] := rfl
lemma tokU_four_one : tokU 4 1 = [0, 4, 4, 4, 4, 2] := rfl
lemma tokV_one : tokV 1 = [4, 3, 2] := rfl

/-- The word denoted by a list of tokens. -/
inductive Tok where
  | U : ℕ → ℕ → Tok
  | V : ℕ → Tok
  deriving DecidableEq, Repr

/-- The tape word of a single token. -/
def Tok.word : Tok → List Sym
  | .U a b => tokU a b
  | .V c => tokV c

/-- The tape word of a list of tokens. -/
def tokWord (ts : List Tok) : List Sym := (ts.map Tok.word).flatten

@[simp] lemma tokWord_nil : tokWord [] = [] := rfl

@[simp] lemma tokWord_cons (t : Tok) (ts : List Tok) :
    tokWord (t :: ts) = t.word ++ tokWord ts := by
  simp [tokWord]

lemma tokWord_append (ts us : List Tok) :
    tokWord (ts ++ us) = tokWord ts ++ tokWord us := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [ih]

end BB25
