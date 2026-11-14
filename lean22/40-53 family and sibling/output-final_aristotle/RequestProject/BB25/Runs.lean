/-
# Block runs, the counter, the decrement and the overflow

The member-independent execution layer shared by every proof of the project.

* `BRun b4 c c' k`: the block simulator `bstep b4` runs from `c` to `c'` in
  `k` base steps; `BRun.sound` turns it into a run of the Turing machine and
  `BRun.not_halts` transports non-halting backwards along it.
* `cval`: the value of the left stack read as a mixed-digit counter
  (`X = 11` bit 0, `Z = 01` bit 1, `W = 03` shift), and `CStack`, the
  well-formed counter stacks resting on the left end `L = ^11`.
* `cdec`: the decrement as an operation on the stack (the borrow);
  `brun_cdec_of`: one excursion of the head into a stack of positive counter
  is exactly one decrement (`cdec_cval`), leaving the right tape untouched.
* `ofw`: the word deposited by the overflow; `brun_overflow_of`: an excursion
  into a stack of counter `0` walks off its bottom, writing `ofw` onto the
  right tape, and arrives at the left end in state `<A`.
-/
import RequestProject.BB25.Blocks
import RequestProject.BB25.Nonhalt

namespace BB25

variable {b4 : Option (Sym × Dir × St)}

/-! ## Composition of block runs -/

/-- Composition of block runs. -/
theorem bsteps_comp {b4 : Option (Sym × Dir × St)} :
    ∀ {m n : ℕ} {c c₁ c₂ : BCfg} {k₁ k₂ : ℕ},
      bsteps b4 m c = some (c₁, k₁) → bsteps b4 n c₁ = some (c₂, k₂) →
        bsteps b4 (m + n) c = some (c₂, k₁ + k₂) := by
  intro m
  induction m with
  | zero =>
      intro n c c₁ c₂ k₁ k₂ h1 h2
      simp only [bsteps, Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      simpa using h2
  | succ m ih =>
      intro n c c₁ c₂ k₁ k₂ h1 h2
      rw [bsteps, Option.bind_eq_some_iff] at h1
      obtain ⟨⟨d, j⟩, hb, h1⟩ := h1
      rw [Option.map_eq_some_iff] at h1
      obtain ⟨⟨d', j'⟩, hr, he⟩ := h1
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have : bsteps b4 (m + n) d = some (c₂, j' + k₂) := ih hr h2
      rw [show m + 1 + n = (m + n) + 1 by omega, bsteps, hb]
      simp only [Option.bind_some, this, Option.map_some]
      exact congrArg some (by simp [Prod.ext_iff]; omega)

/-! ## Multi-step block runs and the left-end spinout of the sweep -/

/-- `BRun b4 c c' k`: the block simulation gets from `c` to `c'` in some number
of block steps, costing exactly `k` base steps of the Turing machine. -/
def BRun (b4 : Option (Sym × Dir × St)) (c c' : BCfg) (k : ℕ) : Prop :=
  ∃ n, bsteps b4 n c = some (c', k)

theorem BRun.refl (c : BCfg) : BRun b4 c c 0 := ⟨0, rfl⟩

theorem BRun.of_step {c c' : BCfg} {k : ℕ} (h : bstep b4 c = some (c', k)) :
    BRun b4 c c' k :=
  ⟨1, by rw [bsteps, h]; simp [bsteps]⟩

theorem BRun.trans {c c₁ c₂ : BCfg} {k₁ k₂ : ℕ}
    (h₁ : BRun b4 c c₁ k₁) (h₂ : BRun b4 c₁ c₂ k₂) : BRun b4 c c₂ (k₁ + k₂) := by
  obtain ⟨n, h₁⟩ := h₁
  obtain ⟨m, h₂⟩ := h₂
  exact ⟨n + m, bsteps_comp h₁ h₂⟩

theorem BRun.head {c c₁ c₂ : BCfg} {k₁ k₂ : ℕ} (h : bstep b4 c = some (c₁, k₁))
    (h₂ : BRun b4 c₁ c₂ k₂) : BRun b4 c c₂ (k₁ + k₂) :=
  (BRun.of_step h).trans h₂

/-- A block run is a run of the Turing machine. -/
theorem BRun.sound {c c' : BCfg} {k : ℕ} (h : BRun b4 c c' k) :
    steps (M b4) k c.den = some c'.den := by
  obtain ⟨n, h⟩ := h
  exact bsteps_sound b4 n c c' k h

/-- If the machine does not halt from the end of a block run, it does not halt
from its beginning either. -/
theorem BRun.not_halts {c c' : BCfg} {k : ℕ} (h : BRun b4 c c' k)
    (hc : ¬ Halts (M b4) c'.den) : ¬ Halts (M b4) c.den :=
  fun hh => hc (hh.of_run h.sound)

/-- The `<B1` head at the left end: the machine never halts. -/
theorem not_halts_Bt_L (rt : List RB) :
    ¬ Halts (M b4) (BCfg.den ⟨[.L], .Bt, rt⟩) :=
  not_halts_leftend_B1 (denR rt)

/-! ## The counter value of the left stack -/

/-- The value of the shift-overflow counter carried by the left stack.
Written as a recursion from the top of the stack (`lt` starts next to the
head), it is the number of further round trips the head can make before it
reaches the left end. -/
def cval : List LB → ℕ
  | .X :: s => 2 * cval s
  | .Z :: s => 2 * cval s + 1
  | .W :: s => cval s / 2
  | _ => 0

@[simp] theorem cval_X (s : List LB) : cval (.X :: s) = 2 * cval s := rfl
@[simp] theorem cval_Z (s : List LB) : cval (.Z :: s) = 2 * cval s + 1 := rfl
@[simp] theorem cval_W (s : List LB) : cval (.W :: s) = cval s / 2 := rfl
@[simp] theorem cval_L (s : List LB) : cval (.L :: s) = 0 := rfl
@[simp] theorem cval_nil : cval [] = 0 := rfl

/-- A well-formed counter stack: `03`, `11`, `01` blocks resting on the left
end `^11`. -/
inductive CStack : List LB → Prop
  | base : CStack [.L]
  | consW {s : List LB} : CStack s → CStack (.W :: s)
  | consX {s : List LB} : CStack s → CStack (.X :: s)
  | consZ {s : List LB} : CStack s → CStack (.Z :: s)

theorem CStack.ne_nil {s : List LB} (h : CStack s) : s ≠ [] := by
  cases h <;> simp

/-- The pending digit of a phase: `true` is `2>`, `false` is `1>`. -/
def pd : Bool → RB
  | true => .P2
  | false => .P1

/-! ## The decrement and the overflow, as operations on the stack -/

/-- The decrement of the block stack, with a step budget (the budget is always
taken to be the length of the stack; see `cdec`). -/
def cdecF : ℕ → List LB → List LB
  | 0, s => s
  | _ + 1, [] => []
  | _ + 1, .Z :: s => .X :: s
  | n + 1, .X :: s => .Z :: cdecF n s
  | n + 1, .W :: s => .W :: cdecF n (cdecF n s)
  | _ + 1, s => s

theorem cdecF_length : ∀ (n : ℕ) (s : List LB), (cdecF n s).length = s.length := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      match s with
      | [] => rfl
      | .Z :: s => rfl
      | .X :: s => simpa [cdecF] using ih s
      | .W :: s => simp [cdecF, ih]
      | .L :: s => rfl
      | .J :: s => rfl
      | .J1 :: s => rfl
      | .J0 :: s => rfl
      | .K0 :: s => rfl
      | .K1 :: s => rfl

theorem cdecF_stable : ∀ (n m : ℕ) (s : List LB), s.length ≤ n → s.length ≤ m →
    cdecF n s = cdecF m s := by
  intro n
  induction n with
  | zero =>
      intro m s hn _
      have : s = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hn)
      subst this
      cases m <;> rfl
  | succ n ih =>
      intro m s hn hm
      match s with
      | [] => cases m <;> rfl
      | .Z :: s => cases m with
          | zero => simp at hm
          | succ m => rfl
      | .L :: s => cases m with
          | zero => simp at hm
          | succ m => rfl
      | .J :: s => cases m with
          | zero => simp at hm
          | succ m => rfl
      | .J1 :: s => cases m with
          | zero => simp at hm
          | succ m => rfl
      | .J0 :: s => cases m with
          | zero => simp at hm
          | succ m => rfl
      | .K0 :: s => cases m with
          | zero => simp at hm
          | succ m => rfl
      | .K1 :: s => cases m with
          | zero => simp at hm
          | succ m => rfl
      | .X :: s => cases m with
          | zero => simp at hm
          | succ m =>
              have h1 : s.length ≤ n := by simpa using hn
              have h2 : s.length ≤ m := by simpa using hm
              simp only [cdecF]
              rw [ih m s h1 h2]
      | .W :: s => cases m with
          | zero => simp at hm
          | succ m =>
              have h1 : s.length ≤ n := by simpa using hn
              have h2 : s.length ≤ m := by simpa using hm
              have hin : cdecF n s = cdecF m s := ih m s h1 h2
              have hlen : (cdecF m s).length ≤ n := by rw [cdecF_length]; exact h1
              have hlen' : (cdecF m s).length ≤ m := by rw [cdecF_length]; exact h2
              simp only [cdecF]
              rw [hin, ih m (cdecF m s) hlen hlen']

/-- **The decrement of the counter, on the stack.**  One head excursion
rewrites the stack exactly like this. -/
def cdec (s : List LB) : List LB := cdecF s.length s

@[simp] theorem cdec_nil : cdec [] = [] := rfl

@[simp] theorem cdec_length (s : List LB) : (cdec s).length = s.length := cdecF_length _ _

/-- A `01` block is a `1` bit: the borrow stops there. -/
@[simp] theorem cdec_Z (s : List LB) : cdec (.Z :: s) = .X :: s := rfl

/-- A `11` block is a `0` bit: the borrow travels on. -/
@[simp] theorem cdec_X (s : List LB) : cdec (.X :: s) = .Z :: cdec s := rfl

/-- **A shift digit costs two decrements.**  This is what makes the counter a
*mixed-digit* one: a borrow crossing a `03` block has to be paid for twice. -/
@[simp] theorem cdec_W (s : List LB) : cdec (.W :: s) = .W :: cdec (cdec s) := by
  show cdecF (s.length + 1) (.W :: s) = _
  simp only [cdecF, cdec]
  rw [cdecF_stable s.length s.length s (le_refl _) (le_refl _),
    cdecF_stable s.length (cdecF s.length s).length (cdecF s.length s)
      (by rw [cdecF_length]) (le_refl _)]

@[simp] theorem cdec_L (s : List LB) : cdec (.L :: s) = .L :: s := rfl

theorem cdec_aux : ∀ (n : ℕ) (s : List LB), s.length ≤ n → CStack s → 1 ≤ cval s →
    CStack (cdec s) ∧ cval (cdec s) = cval s - 1 := by
  intro n
  induction n with
  | zero =>
      intro s hlen hst _
      exact absurd (List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)) hst.ne_nil
  | succ n ih =>
      intro s hlen hst hv
      cases hst with
      | base => exact absurd hv (by simp)
      | @consZ s hs => exact ⟨by rw [cdec_Z]; exact hs.consX, by rw [cdec_Z, cval_X, cval_Z]; omega⟩
      | @consX s hs =>
          have hs1 : 1 ≤ cval s := by simp at hv; omega
          obtain ⟨h1, h2⟩ := ih s (by simpa using hlen) hs hs1
          exact ⟨by rw [cdec_X]; exact h1.consZ, by rw [cdec_X, cval_Z, cval_X, h2]; omega⟩
      | @consW s hs =>
          have hs2 : 2 ≤ cval s := by simp at hv; omega
          obtain ⟨h1, h2⟩ := ih s (by simpa using hlen) hs (by omega)
          obtain ⟨h3, h4⟩ := ih (cdec s) (by rw [cdec_length]; simpa using hlen) h1 (by omega)
          refine ⟨by rw [cdec_W]; exact h3.consW, ?_⟩
          rw [cdec_W, cval_W, cval_W, h4, h2]
          omega

/-- The decrement keeps the stack well formed. -/
theorem cdec_CStack {s : List LB} (hst : CStack s) (hv : 1 ≤ cval s) : CStack (cdec s) :=
  (cdec_aux s.length s (le_refl _) hst hv).1

/-- The decrement decrements the value. -/
theorem cdec_cval {s : List LB} (hst : CStack s) (hv : 1 ≤ cval s) :
    cval (cdec s) = cval s - 1 :=
  (cdec_aux s.length s (le_refl _) hst hv).2

/-- **The machine performs `cdec`.**  A head that enters a nonzero counter in
state `<A` comes back out in state `A>` with the stack rewritten by `cdec`, the
right-hand tape untouched. -/
theorem brun_cdec : ∀ (n : ℕ) (s : List LB), s.length ≤ n → CStack s → 1 ≤ cval s →
    ∀ rt : List RB, ∃ k, BRun (b4 := b4) ⟨s, .Lt, rt⟩ ⟨cdec s, .Rt, rt⟩ k := by
  intro n
  induction n with
  | zero =>
      intro s hlen hst _ _
      exact absurd (List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)) hst.ne_nil
  | succ n ih =>
      intro s hlen hst hv rt
      cases hst with
      | base => exact absurd hv (by simp)
      | @consX s hs =>
          have hlen' : s.length ≤ n := by simpa using hlen
          have hs1 : 1 ≤ cval s := by simp at hv; omega
          obtain ⟨k, hrun⟩ := ih s hlen' hs hs1 (.Y :: rt)
          refine ⟨2 + (k + 2), ?_⟩
          rw [cdec_X]
          exact BRun.head (show bstep b4 ⟨.X :: s, .Lt, rt⟩ = some (⟨s, .Lt, .Y :: rt⟩, 2) from rfl)
            (hrun.trans (BRun.of_step (show bstep b4 ⟨cdec s, .Rt, .Y :: rt⟩
              = some (⟨.Z :: cdec s, .Rt, rt⟩, 2) from rfl)))
      | @consZ s hs =>
          refine ⟨3, ?_⟩
          rw [cdec_Z]
          exact BRun.of_step
            (show bstep b4 ⟨.Z :: s, .Lt, rt⟩ = some (⟨.X :: s, .Rt, rt⟩, 3) from rfl)
      | @consW s hs =>
          have hlen' : s.length ≤ n := by simpa using hlen
          have hs2 : 2 ≤ cval s := by simp at hv; omega
          obtain ⟨k₁, hrun₁⟩ := ih s hlen' hs (by omega) (.X :: rt)
          have hv' : cval (cdec s) = cval s - 1 := cdec_cval hs (by omega)
          have hlen'' : (cdec s).length ≤ n := by rw [cdec_length]; exact hlen'
          obtain ⟨k₂, hrun₂⟩ := ih (cdec s) hlen'' (cdec_CStack hs (by omega)) (by omega) (.V :: rt)
          refine ⟨2 + (k₁ + (1 + (k₂ + 2))), ?_⟩
          rw [cdec_W]
          exact BRun.head (show bstep b4 ⟨.W :: s, .Lt, rt⟩ = some (⟨s, .Lt, .X :: rt⟩, 2) from rfl)
            (hrun₁.trans (BRun.head (show bstep b4 ⟨cdec s, .Rt, .X :: rt⟩
                = some (⟨cdec s, .Lt, .V :: rt⟩, 1) from rfl)
              (hrun₂.trans (BRun.of_step (show bstep b4 ⟨cdec (cdec s), .Rt, .V :: rt⟩
                = some (⟨.W :: cdec (cdec s), .Rt, rt⟩, 2) from rfl)))))

/-- **The decrement of the counter, explicitly.** -/
theorem brun_cdec_of {s : List LB} (hst : CStack s) (hv : 1 ≤ cval s) (rt : List RB) :
    ∃ k, BRun (b4 := b4) ⟨s, .Lt, rt⟩ ⟨cdec s, .Rt, rt⟩ k :=
  brun_cdec s.length s (le_refl _) hst hv rt

/-- The word the overflow deposits on the right-hand tape, with a step budget
(always the length of the stack; see `ofw`). -/
def ofwF : ℕ → List LB → List RB
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, .X :: s => ofwF n s ++ [.Y]
  | n + 1, .W :: s => if cval s = 0 then ofwF n s ++ [.X] else ofwF n (cdec s) ++ [.V]
  | _ + 1, _ => []

theorem ofwF_stable : ∀ (n m : ℕ) (s : List LB), s.length ≤ n → s.length ≤ m →
    ofwF n s = ofwF m s := by
  intro n
  induction n with
  | zero =>
      intro m s hn _
      have : s = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hn)
      subst this
      cases m <;> rfl
  | succ n ih =>
      intro m s hn hm
      match s with
      | [] => cases m <;> rfl
      | .Z :: s => cases m with
          | zero => simp at hm
          | succ m => rfl
      | .L :: s => cases m with
          | zero => simp at hm
          | succ m => rfl
      | .J :: s => cases m with
          | zero => simp at hm
          | succ m => rfl
      | .J1 :: s => cases m with
          | zero => simp at hm
          | succ m => rfl
      | .J0 :: s => cases m with
          | zero => simp at hm
          | succ m => rfl
      | .K0 :: s => cases m with
          | zero => simp at hm
          | succ m => rfl
      | .K1 :: s => cases m with
          | zero => simp at hm
          | succ m => rfl
      | .X :: s => cases m with
          | zero => simp at hm
          | succ m =>
              have h1 : s.length ≤ n := by simpa using hn
              have h2 : s.length ≤ m := by simpa using hm
              simp only [ofwF]
              rw [ih m s h1 h2]
      | .W :: s => cases m with
          | zero => simp at hm
          | succ m =>
              have h1 : s.length ≤ n := by simpa using hn
              have h2 : s.length ≤ m := by simpa using hm
              have hlen : (cdec s).length ≤ n := by rw [cdec_length]; exact h1
              have hlen' : (cdec s).length ≤ m := by rw [cdec_length]; exact h2
              simp only [ofwF]
              rw [ih m s h1 h2, ih m (cdec s) hlen hlen']

/-- **The word the overflow deposits.**  Read from the head outwards, it is the
whole left stack translated block for block into the right-hand digits. -/
def ofw (s : List LB) : List RB := ofwF s.length s

@[simp] theorem ofw_nil : ofw [] = [] := rfl
@[simp] theorem ofw_L (s : List LB) : ofw (.L :: s) = [] := rfl
@[simp] theorem ofw_Z (s : List LB) : ofw (.Z :: s) = [] := rfl

/-- A `11` block of the counter leaves a `22` block on the tape. -/
@[simp] theorem ofw_X (s : List LB) : ofw (.X :: s) = ofw s ++ [.Y] := rfl

/-- A `03` block leaves an `11` block, or a `21` block if the head still had a
decrement to spend below it. -/
@[simp] theorem ofw_W (s : List LB) :
    ofw (.W :: s) = if cval s = 0 then ofw s ++ [.X] else ofw (cdec s) ++ [.V] := by
  show ofwF (s.length + 1) (.W :: s) = _
  simp only [ofwF, ofw]
  rw [ofwF_stable s.length s.length s (le_refl _) (le_refl _),
    ofwF_stable s.length (cdec s).length (cdec s) (by rw [cdec_length]) (le_refl _)]

/--
**The overflow re-encodes the counter onto the tape.**  If the counter is `0`
the head walks off the bottom of the stack and reaches the left end `^11`, and
the tape it leaves behind is the old tape with the word `ofw lt` — the whole
stack, translated block for block into right-hand digits — in front of it.
This word is the input of the next reset phase.
-/
theorem brun_overflow_word : ∀ (n : ℕ) (s : List LB), s.length ≤ n → CStack s → cval s = 0 →
    ∀ rt : List RB, ∃ k, BRun (b4 := b4) ⟨s, .Lt, rt⟩ ⟨[.L], .Lt, ofw s ++ rt⟩ k := by
  intro n
  induction n with
  | zero =>
      intro s hlen hst _ _
      exact absurd (List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)) hst.ne_nil
  | succ n ih =>
      intro s hlen hst hv rt
      cases hst with
      | base => exact ⟨0, by simpa using BRun.refl (b4 := b4) _⟩
      | @consZ s hs => exact absurd hv (by simp)
      | @consX s hs =>
          have hlen' : s.length ≤ n := by simpa using hlen
          have h0 : cval s = 0 := by simp at hv; omega
          obtain ⟨k, hrun⟩ := ih s hlen' hs h0 (.Y :: rt)
          refine ⟨2 + k, ?_⟩
          rw [ofw_X]
          simpa using
            BRun.head (show bstep b4 ⟨.X :: s, .Lt, rt⟩ = some (⟨s, .Lt, .Y :: rt⟩, 2) from rfl) hrun
      | @consW s hs =>
          have hlen' : s.length ≤ n := by simpa using hlen
          have h1 : cval s ≤ 1 := by simp at hv; omega
          rcases Nat.eq_zero_or_pos (cval s) with h0 | h0
          · obtain ⟨k, hrun⟩ := ih s hlen' hs h0 (.X :: rt)
            refine ⟨2 + k, ?_⟩
            rw [ofw_W, if_pos h0]
            simpa using
              BRun.head (show bstep b4 ⟨.W :: s, .Lt, rt⟩ = some (⟨s, .Lt, .X :: rt⟩, 2) from rfl)
                hrun
          · obtain ⟨k₁, hrun₁⟩ := brun_cdec_of (b4 := b4) hs h0 (.X :: rt)
            have hlen'' : (cdec s).length ≤ n := by rw [cdec_length]; exact hlen'
            have hv' : cval (cdec s) = 0 := by rw [cdec_cval hs (by omega)]; omega
            obtain ⟨k₂, hrun₂⟩ := ih (cdec s) hlen'' (cdec_CStack hs (by omega)) hv' (.V :: rt)
            refine ⟨2 + (k₁ + (1 + k₂)), ?_⟩
            rw [ofw_W, if_neg (by omega)]
            have hrun : BRun (b4 := b4) ⟨.W :: s, .Lt, rt⟩ ⟨[.L], .Lt, ofw (cdec s) ++ (.V :: rt)⟩
                (2 + (k₁ + (1 + k₂))) :=
              BRun.head (show bstep b4 ⟨.W :: s, .Lt, rt⟩ = some (⟨s, .Lt, .X :: rt⟩, 2) from rfl)
                (hrun₁.trans (BRun.head (show bstep b4 ⟨cdec s, .Rt, .X :: rt⟩
                    = some (⟨cdec s, .Lt, .V :: rt⟩, 1) from rfl) hrun₂))
            simpa using hrun

/-- **The overflow, packaged.** -/
theorem brun_overflow_of {s : List LB} (hst : CStack s) (hv : cval s = 0) (rt : List RB) :
    ∃ k, BRun (b4 := b4) ⟨s, .Lt, rt⟩ ⟨[.L], .Lt, ofw s ++ rt⟩ k :=
  brun_overflow_word s.length s (le_refl _) hst hv rt

end BB25
