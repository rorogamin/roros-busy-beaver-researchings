/-
# `0LB`: the single-return invariant

A Z checkpoint `L c Z <B1 22^r 1` is described by a reset word `w` and a debt
`k`: its core is `c = D^k (T w)`.  The invariant `ZInv w k r` of the submitted
argument (Section 4) asks

* `w = YYY v` with `v` a Dyck prefix (the bottom three bit *positions* are
  unmatched);
* the energy pays for the debt, `k ≤ erun w 0`, and the counter
  `a = rrun w 0 - k` is at least two;
* the height `h = ht w` is at least five, the decoded value `b = trun w 0 0`
  satisfies `23·2^h ≤ 24 (b + 1)` and the decoded energy `F = etrun w 0 0`
  satisfies `3·2^(h-2) + 4 ≤ F`;
* `r ≥ 4`.

`zinv_return` is the main return theorem: from such a checkpoint the machine
runs for a positive number of steps to another Z checkpoint satisfying the
invariant.  (The counter density bound is used with the height `h`, which is
weaker than the decoded height of the document; the density bounds of
`density_bounds` close it all the same.)
-/
import RequestProject.BB25.Prefix.LB0.Scan

namespace BB25.Prefix

open BB25

/-- **The invariant of a Z checkpoint of `0LB`**, for the core `D^k (T w)`. -/
structure ZInv (w : List RB) (k r : ℕ) : Prop where
  digs : Digs w
  prot : ∃ v, w = [.Y, .Y, .Y] ++ v ∧ DyckPre v
  energy : (k : ℤ) ≤ erun w 0
  counter : (k : ℤ) + 2 ≤ rrun w 0
  height : ∃ h : ℕ, ht w = h ∧ 5 ≤ h ∧ 23 * 2 ^ h ≤ 24 * (trun w 0 0 + 1) ∧
    3 * 2 ^ (h - 2) + 4 ≤ etrun w 0 0
  right : 4 ≤ r

/-! ## Dyck prefixes -/

theorem Pops.bal {z : List RB} (hz : Pops z) : bal z = -(z.length : ℤ) := by
  induction z with
  | nil => simp
  | cons c z ihz =>
      rcases hz c (by simp) with rfl | rfl
      · simp [ihz (fun d hd => hz d (by simp [hd]))]; ring
      · simp [ihz (fun d hd => hz d (by simp [hd]))]; ring

theorem DyckPre.append_pops {x η : List RB} (hx : DyckPre x) (hη : Pops η)
    (hlen : (η.length : ℤ) ≤ bal x) : DyckPre (x ++ η) := by
  induction η using List.reverseRecOn with
  | nil => simpa using hx
  | append_singleton η b ih =>
      have hp := hη.of_append
      have hb : b = RB.X ∨ b = RB.V := hp.2 b (by simp)
      have hle : (η.length : ℤ) ≤ bal x := by simp at hlen; omega
      have ih' := ih hp.1 hle
      rw [← List.append_assoc]
      refine DyckPre.snoc ih' ?_
      have hbal : ∀ z : List RB, Pops z → bal z = -(z.length : ℤ) := by
        intro z hz
        induction z with
        | nil => simp
        | cons c z ihz =>
            rcases hz c (by simp) with rfl | rfl
            · simp [ihz (fun d hd => hz d (by simp [hd]))]; ring
            · simp [ihz (fun d hd => hz d (by simp [hd]))]; ring
      rw [List.append_assoc, bal_append, hbal _ hη]
      simp at hlen ⊢
      omega

theorem dyckPre_replicate_Y (n : ℕ) : DyckPre (List.replicate n RB.Y) := by
  induction n with
  | zero => exact DyckPre.nil
  | succ n ih => rw [List.replicate_succ]; exact ih.cons_Y

/-- The clock buffer is a balanced word. -/
theorem buffer_dyck {r : ℕ} (hr : 1 ≤ r) :
    DyckPre (List.replicate r RB.Y ++ [RB.V] ++ List.replicate (r - 1) RB.X) ∧
      bal (List.replicate r RB.Y ++ [RB.V] ++ List.replicate (r - 1) RB.X) = 0 := by
  have hp : Pops ([RB.V] ++ List.replicate (r - 1) RB.X) := by
    intro b hb
    simp only [List.mem_append, List.mem_singleton, List.mem_replicate] at hb
    rcases hb with rfl | ⟨-, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hlen : (([RB.V] ++ List.replicate (r - 1) RB.X).length : ℤ) = r := by
    simp; omega
  refine ⟨?_, ?_⟩
  · rw [List.append_assoc]
    exact (dyckPre_replicate_Y r).append_pops hp (by rw [hlen, bal_replicate_Y])
  · rw [bal_append, bal_append, bal_replicate_Y]
    have : bal (List.replicate (r - 1) RB.X) = -((r - 1 : ℕ) : ℤ) := by
      induction (r - 1) with
      | zero => simp
      | succ n ih => rw [List.replicate_succ, bal_X, ih]; push_cast; ring
    rw [this]
    simp
    omega

/-! ## Closing the two quantitative bounds -/

/-- **The quantitative bounds at a new checkpoint** (Section 8). -/
theorem height_close {v : List RB} (hv : Digs v) (hd : DyckPre v)
    (hL : 4 ≤ bal ([RB.Y, RB.Y, RB.Y] ++ v)) (hh : 6 ≤ ht ([RB.Y, RB.Y, RB.Y] ++ v)) :
    ∃ h : ℕ, ht ([RB.Y, RB.Y, RB.Y] ++ v) = h ∧ 5 ≤ h ∧
      23 * 2 ^ h ≤ 24 * (trun ([RB.Y, RB.Y, RB.Y] ++ v) 0 0 + 1) ∧
      3 * 2 ^ (h - 2) + 4 ≤ etrun ([RB.Y, RB.Y, RB.Y] ++ v) 0 0 := by
  set w := [RB.Y, RB.Y, RB.Y] ++ v with hw
  have hwd : Digs w := Digs.append (by intro b hb; simp at hb; rw [hb]; exact Or.inl rfl) hv
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, bal w = L := ⟨(bal w).toNat, by omega⟩
  obtain ⟨h, hhdef⟩ : ∃ h : ℕ, ht w = h := ⟨(ht w).toNat, by omega⟩
  obtain ⟨A, B⟩ := density_bounds hv hd hLdef
  set q := qcnt w 0 with hq
  have hle : ht w ≤ bal w + 2 * (q : ℤ) := ht_le_bal_qcnt hwd 0
  have hhE : h ≤ L + 2 * q := by omega
  have hpow : (2 : ℤ) ^ h ≤ 2 ^ (L + 2 * q) := pow_le_pow_right₀ (by norm_num) hhE
  have hL4 : 4 ≤ L := by omega
  have hpowL : (16 : ℤ) ≤ 2 ^ L := by
    calc (16 : ℤ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) hL4
  refine ⟨h, hhdef, by omega, by linarith, ?_⟩
  have hh6 : 6 ≤ h := by omega
  obtain ⟨g, rfl⟩ : ∃ g, h = g + 2 := ⟨h - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hg : (2 : ℤ) ^ (g + 2) = 4 * 2 ^ g := by rw [pow_add]; ring
  rw [hg] at hpow
  rcases Nat.eq_or_lt_of_le hh6 with h6 | h7
  · have : g = 4 := by omega
    subst this
    norm_num at hpow ⊢
    linarith
  · have h32 : (32 : ℤ) ≤ 2 ^ g := by
      calc (32 : ℤ) = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ g := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith

/-! ## The arithmetic of the return -/

/-- The energy of the whole drain word is nonnegative (Section 5). -/
theorem drain_energy {F : ℤ} {h t : ℕ} (hh : 5 ≤ h) (hF : 3 * 2 ^ (h - 2) + 4 ≤ F)
    (ht : t ≤ h - 2) {d : RB} (hd : d = RB.X ∨ d = RB.V) :
    6 * (2 ^ t - 1) ≤ 4 * estep d F - 2 := by
  obtain ⟨g, rfl⟩ : ∃ g, h = g + 5 := ⟨h - 5, by omega⟩
  have e1 : (2 : ℤ) ^ (g + 5 - 2) = 8 * 2 ^ g := by
    rw [show g + 5 - 2 = g + 3 by omega, pow_add]; ring
  have e2 : (2 : ℤ) ^ t ≤ 8 * 2 ^ g := by
    rw [← e1]; exact pow_le_pow_right₀ (by norm_num) ht
  rw [e1] at hF
  have hg : (1 : ℤ) ≤ 2 ^ g := by
    have : (0 : ℤ) < 2 ^ g := by positivity
    omega
  rcases hd with rfl | rfl
  · simp only [estep_X]
    omega
  · simp only [estep_V]
    omega

/-- The counter at a buffer stop is at least two (equations (31)–(32)). -/
theorem buffer_counter {b : ℤ} {h t n1 : ℕ} (hh : 5 ≤ h) (hb : 23 * 2 ^ h ≤ 24 * (b + 1))
    (ht : t ≤ h - 2) (hn : n1 + 6 ≤ 6 * 2 ^ t) {d : RB} (hd : d = RB.X ∨ d = RB.V) :
    (n1 : ℤ) + 8 ≤ 4 * (rstep d b + 1) := by
  obtain ⟨g, rfl⟩ : ∃ g, h = g + 5 := ⟨h - 5, by omega⟩
  have e1 : (2 : ℤ) ^ (g + 5 - 2) = 8 * 2 ^ g := by
    rw [show g + 5 - 2 = g + 3 by omega, pow_add]; ring
  have e2 : (2 : ℤ) ^ t ≤ 8 * 2 ^ g := by
    rw [← e1]; exact pow_le_pow_right₀ (by norm_num) ht
  have e3 : (2 : ℤ) ^ (g + 5) = 32 * 2 ^ g := by rw [pow_add]; ring
  rw [e3] at hb
  have hn' : (n1 : ℤ) + 6 ≤ 6 * 2 ^ t := by exact_mod_cast hn
  have hg : (1 : ℤ) ≤ 2 ^ g := by
    have : (0 : ℤ) < 2 ^ g := by positivity
    omega
  rcases hd with rfl | rfl
  · simp only [rstep_X]
    omega
  · simp only [rstep_V]
    omega

/-- The counter at a buffer stop, from the bound of `buffer_counter`. -/
theorem counter_close {N n1 s : ℕ} {x : ℤ} (hN : N = 2 ^ s * (n1 + 6))
    (hbc : (n1 : ℤ) + 8 ≤ 4 * (x + 1)) : ((N - 1 : ℕ) : ℤ) + 2 ≤ 2 ^ (s + 2) * (x + 1) - 1 := by
  have hpow1 : (1 : ℕ) ≤ 2 ^ s := Nat.one_le_two_pow
  have hN6 : 1 ≤ N := by
    rw [hN]
    calc 1 ≤ 1 * (n1 + 6) := by omega
      _ ≤ 2 ^ s * (n1 + 6) := Nat.mul_le_mul_right _ hpow1
  have hNc : ((N - 1 : ℕ) : ℤ) = (2 : ℤ) ^ s * ((n1 : ℤ) + 6) - 1 := by
    rw [Nat.cast_sub hN6, hN]; push_cast; ring
  rw [hNc, pow_add]
  have hps : (1 : ℤ) ≤ 2 ^ s := by exact_mod_cast hpow1
  have h2 : (2 : ℤ) ^ s * ((n1 : ℤ) + 8) ≤ 2 ^ s * (4 * (x + 1)) :=
    mul_le_mul_of_nonneg_left hbc (by positivity)
  nlinarith

/-! ## The return -/

variable {b4 : Option (Sym × Dir × St)}

theorem ht_replicate_Y (n : ℕ) : ht (List.replicate n RB.Y) = n := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, ht_Y, ih]; push_cast; ring

theorem ht_replicate_X (n : ℕ) : ht (List.replicate n RB.X) = -(n : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, ht_X, ih]; push_cast; ring

theorem digs_replicate {b : RB} (hb : Dig b) (n : ℕ) : Digs (List.replicate n b) := by
  intro c hc
  rw [List.mem_replicate] at hc
  rw [hc.2]; exact hb

theorem zinv_return {w : List RB} {k r : ℕ} (hI : ZInv w k r) :
    ∃ (w' : List RB) (k' r' T : ℕ), 0 < T ∧
      BRun b4_0LB (zCfg (dpow k (TW w)) r) (zCfg (dpow k' (TW w')) r') T ∧ ZInv w' k' r' := by
  obtain ⟨hw, ⟨v, hwv, hdv⟩, hE, hC, ⟨h, hh, hh5, hB, hF⟩, hr⟩ := hI
  have hkr : (k : ℤ) ≤ rrun w 0 := by omega
  have hk2 : ((k + 2 : ℕ) : ℤ) ≤ rrun w 0 := by push_cast; omega
  obtain ⟨hst, hadm, hg, hcv, hbv, hpd, hnb⟩ := dpow_TW_facts hw hkr
  obtain ⟨hst2, hadm2, hg2, hcv2, hbv2, hpd2, hnb2⟩ := dpow_TW_facts hw hk2
  set c := dpow k (TW w) with hc
  set c2 := dpow (k + 2) (TW w) with hc2
  set b := trun w 0 0 with hbdef
  set F := etrun w 0 0 with hFdef
  have ha2 : 2 ≤ cval c := by omega
  have hcv2' : cval c2 = cval c - 2 := by push_cast at hcv2; omega
  have hab : (cval c : ℤ) ≤ b := by have := hg.head; rwa [hbv] at this
  have hnb' : nbit c - nsh c = h := by have := hadm.head; omega
  have hlt : cval c < 2 ^ h := by have := cval_lt_two_pow hst hadm; rwa [hnb'] at this
  have hv : Digs v := by rw [hwv] at hw; exact hw.of_append.2
  have hhtv : ht v = (h : ℤ) - 3 := by rw [hwv, ht_append] at hh; simp at hh; omega
  -- the parity digit
  set d : RB := if cval c2 % 2 = 1 then RB.V else RB.X with hd
  have hdXV : d = RB.X ∨ d = RB.V := by
    by_cases hp : cval c2 % 2 = 1
    · right; simp [hd, hp]
    · left; simp [hd, hp]
  have hdd : Dig d := by
    rcases hdXV with h' | h' <;> rw [h']
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
  have hbald : bal [d] = -1 := by rcases hdXV with h' | h' <;> rw [h'] <;> rfl
  have hhtd : -1 ≤ ht [d] := by rcases hdXV with h' | h' <;> rw [h'] <;> simp
  -- the first part of the run: the `01` branch pops a bit of the core
  have hc2eq : cdec (cdec c) = c2 := rfl
  have h1c : 1 ≤ cval c := by omega
  have hstd : CStack (cdec c) := cdec_CStack_all hst
  have hcvd : cval (cdec c) = cval c - 1 := cdec_cval hst h1c
  obtain ⟨k1, hr1⟩ := brun_cdec_of (b4 := b4_0LB) hst h1c (.X :: .P2 :: ytail r)
  obtain ⟨k2, hr2⟩ := brun_cdec_of (b4 := b4_0LB) hstd (by omega) (.V :: .P2 :: ytail r)
  have hrunA : BRun b4_0LB (zCfg c r) ⟨.W :: c2, .Rt, .P2 :: ytail r⟩ (4 + (k1 + (1 + (k2 + 2)))) :=
    BRun.head (show bstep b4_0LB (zCfg c r) = some (⟨c, .Lt, .X :: .P2 :: ytail r⟩, 4) from rfl)
      (hr1.trans (BRun.head (show bstep b4_0LB ⟨cdec c, .Rt, .X :: .P2 :: ytail r⟩
          = some (⟨cdec c, .Lt, .V :: .P2 :: ytail r⟩, 1) from rfl)
        (hr2.trans (BRun.of_step (show bstep b4_0LB ⟨cdec (cdec c), .Rt, .V :: .P2 :: ytail r⟩
          = some (⟨.W :: c2, .Rt, .P2 :: ytail r⟩, 2) from rfl)))))
  -- the pending tail and the drain
  set m := cval c / 2 with hm
  have hσcv : cval (.W :: c2) + 1 = m := by simp only [cval_W]; omega
  have hσadm : Adm (.W :: c2) := adm_consW hadm2 (by have := hadm2.head; omega)
  have hσb : 3 * ((cval (.W :: c2) : ℤ) + 1) ≤ 4 * (bval (.W :: c2) + 1) := by
    rw [bval_W, hbv2]
    have hσ' : ((cval (.W :: c2) : ℕ) : ℤ) + 1 = (m : ℤ) := by
      rw [← hσcv]; push_cast; ring
    rw [hσ']
    by_cases hp : cval c2 % 2 = 1
    · rw [if_pos hp]; omega
    · rw [if_neg hp]; omega
  obtain ⟨-, -, kt, hrunT⟩ := exact_tail (b4 := b4_0LB) hst2.consW hσadm hσb (show 1 ≤ r by omega)
  have hpdσ : pdec (.W :: c2) = qw w 0 ++ [d] := by rw [pdec_W, hpd2]
  have hchi : chi (2 ^ (r - 1) * (cval (.W :: c2) + 1)) = List.replicate (r - 1) .X ++ chi m := by
    rw [hσcv]; exact chi_two_pow _ _ (by omega)
  set Q := qw w 0 with hQ
  set P3 := Q ++ [d] ++ List.replicate r .Y ++ [.V] with hP3
  set P4 := P3 ++ List.replicate (r - 1) .X with hP4
  set P5 := P4 ++ chi m with hP5
  have hU : pdec (.W :: c2) ++ List.replicate r .Y ++ [.V]
      ++ chi (2 ^ (r - 1) * (cval (.W :: c2) + 1)) ++ [.V] = P5 ++ [.V] := by
    rw [hpdσ, hchi]; simp [hP5, hP4, hP3, List.append_assoc]
  rw [hU] at hrunT
  -- energies along the drain word
  have hQd : Digs Q := qw_digs hw 0
  have hP3d : Digs P3 := ((hQd.append (Digs.cons hdd Digs.nil)).append
    (digs_replicate (Or.inl rfl) r)).append (Digs.cons (Or.inr (Or.inl rfl)) Digs.nil)
  have hP4d : Digs P4 := hP3d.append (digs_replicate (Or.inr (Or.inr rfl)) _)
  have hEQ : erun Q 0 = F := (etrun_eq_erun_qw w 0 0).symm
  have hEP4 : erun P4 0 = 4 * estep d F - 2 := by
    have : P4 = (Q ++ [d]) ++ (List.replicate r RB.Y ++ [RB.V] ++ List.replicate (r - 1) RB.X) := by
      simp [hP4, hP3, List.append_assoc]
    rw [this, erun_append, erun_buffer hr, erun_append, hEQ, erun_singleton]
  have hm1 : 1 ≤ m := by omega
  have hmlt : m < 2 ^ (h - 2 + 1) := by
    rw [show h - 2 + 1 = h - 1 by omega]
    have : 2 ^ h = 2 * 2 ^ (h - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  set t := (chi m).length with ht_def
  have htle : t ≤ h - 2 := chi_length_le _ _ hm1 hmlt
  have hEP5 : 0 ≤ erun P5 0 := by
    rw [hP5, erun_append, hEP4]
    exact erun_pops_nonneg _ (chi_pops m) _ (drain_energy hh5 hF htle hdXV)
  have hEU : ((0 : ℕ) : ℤ) ≤ erun (P5 ++ [.V]) 0 := by
    rw [erun_append, erun_singleton, estep_V]; simp; omega
  obtain ⟨hrV, hE5⟩ := scan_V_even (b4 := b4_0LB) (u := P5) (n := 0) (j := 1) rfl hEU
  have hrun0 : BRun b4_0LB (zCfg c r) ⟨dpow 0 (TW (P4 ++ chi m)), .Bt, ytail 2⟩
      ((4 + (k1 + (1 + (k2 + 2)))) + (kt + 6)) :=
    hrunA.trans (hrunT.trans hrV)
  have hE5' : ((0 : ℕ) : ℤ) ≤ erun (P4 ++ chi m) 0 := by simpa using hE5
  -- the protected shape of the new word
  have hQv : Q = [RB.Y, RB.Y, RB.Y] ++ qw v 7 := by rw [hQ, hwv, qw_append]; rfl
  have hq7 : DyckPre (qw v 7) := dyckPre_qw hv hdv 7
  have hbq7 : bal (qw v 7) = (h : ℤ) - 3 := by rw [bal_qw hv, hhtv]
  have hq7d : Digs (qw v 7) := qw_digs hv 7
  have hD1 : DyckPre (qw v 7 ++ [d]) := hq7.snoc (by rw [bal_append, hbq7, hbald]; omega)
  have hbD1 : bal (qw v 7 ++ [d]) = (h : ℤ) - 4 := by rw [bal_append, hbq7, hbald]; ring
  have hhtq7 : (h : ℤ) - 3 ≤ ht (qw v 7) := by rw [← hbq7]; exact bal_le_ht hq7d
  rcases scan_pops (chi m) (chi_pops m) P4 0 2 hP4d hE5' with
      ⟨η, t2, k', T, hct, hk', -, h0, hrS⟩ | ⟨n1, T, hn1, hn1b, hrS⟩
  · -- the sweep stops inside the drain digits
    have hηp : Pops η := by
      have := chi_pops m
      rw [hct] at this
      exact this.of_append.1
    have ht2 : 2 ≤ t2.length := h0 rfl
    have hηlen : η.length + 1 + t2.length = t := by rw [ht_def, hct]; simp; omega
    obtain ⟨hBd, hBb⟩ := buffer_dyck (r := r) (by omega)
    set B := List.replicate r RB.Y ++ [RB.V] ++ List.replicate (r - 1) RB.X with hBdef
    have hBdig : Digs B := ((digs_replicate (Or.inl rfl) r).append
      (Digs.cons (Or.inr (Or.inl rfl)) Digs.nil)).append (digs_replicate (Or.inr (Or.inr rfl)) _)
    have hhtB : ht B = 2 := by
      rw [hBdef, ht_append, ht_append, ht_replicate_Y, ht_replicate_X]
      simp
      omega
    set v' := qw v 7 ++ [d] ++ B ++ η with hv'
    have hw' : P4 ++ η = [RB.Y, RB.Y, RB.Y] ++ v' := by
      rw [hP4, hP3, hQv, hv', hBdef]; simp [List.append_assoc]
    have hv'd : Digs v' := ((hq7d.append (Digs.cons hdd Digs.nil)).append hBdig).append hηp.digs
    have hD2 : DyckPre (qw v 7 ++ [d] ++ B) := hD1.append hBd
    have hbD2 : bal (qw v 7 ++ [d] ++ B) = (h : ℤ) - 4 := by rw [bal_append, hbD1, hBb]; ring
    have hv'dy : DyckPre v' := hD2.append_pops hηp (by rw [hbD2]; omega)
    have hbalw : bal ([RB.Y, RB.Y, RB.Y] ++ v') = (h : ℤ) - 1 - η.length := by
      rw [bal_append, hv', bal_append, hbD2, hηp.bal]
      simp
      ring
    have hhtw : 6 ≤ ht ([RB.Y, RB.Y, RB.Y] ++ v') := by
      rw [ht_append, hv', ht_append, ht_append, ht_append, hhtB]
      have := ht_ge_neg_length η
      simp
      omega
    have hXw : RB.X ∈ P4 ++ η :=
      List.mem_append_left _ (List.mem_append_right _ (List.mem_replicate.mpr ⟨by omega, rfl⟩))
    have hcnt := erun_add_two_le_rrun hXw (e := 0) (a := 0) le_rfl
    refine ⟨[RB.Y, RB.Y, RB.Y] ++ v', k', 2 + t2.length,
      (4 + (k1 + (1 + (k2 + 2)))) + (kt + 6) + T, by omega, ?_, ?_⟩
    · rw [← hw']
      exact hrun0.trans hrS
    · refine ⟨Digs.append (by intro x hx; simp at hx; rw [hx]; exact Or.inl rfl) hv'd,
        ⟨v', rfl, hv'dy⟩, by rw [← hw']; exact hk', by rw [← hw']; omega,
        height_close hv'd hv'dy (by rw [hbalw]; omega) hhtw, by omega⟩
  · -- the sweep crosses the drain digits and stops in the buffer
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 4 := ⟨r - 4, by omega⟩
    have hn1' : n1 + 6 ≤ 6 * 2 ^ t := by rw [ht_def]; linarith
    have hP4eq : P4 = P3 ++ List.replicate (s + 3) RB.X := by
      rw [hP4, show s + 4 - 1 = s + 3 by omega]
    rw [hP4eq] at hrS hn1
    obtain ⟨k3, hr3, he3⟩ := scan_Xrun_lb (s + 3) P3 n1 (2 + t) hP3d hn1
    obtain ⟨N, hN⟩ : ∃ N, N = 2 ^ s * (n1 + 6) := ⟨_, rfl⟩
    have hpow1 : (1 : ℕ) ≤ 2 ^ s := Nat.one_le_two_pow
    have hN6 : 6 ≤ N := by
      rw [hN]
      calc 6 ≤ 1 * (n1 + 6) := by omega
        _ ≤ 2 ^ s * (n1 + 6) := Nat.mul_le_mul_right _ hpow1
    have e3 : 2 ^ (s + 3) * (n1 + 6) - 6 = 8 * N - 6 := by
      have : 2 ^ (s + 3) * (n1 + 6) = 8 * N := by rw [hN, pow_add]; ring
      omega
    rw [e3] at hr3 he3
    obtain ⟨hr4, he4⟩ := scan_V_even (b4 := b4_0LB) (u := Q ++ [d] ++ List.replicate (s + 4) RB.Y)
      (n := 8 * N - 6) (j := 2 + t + (s + 3)) (by omega) he3
    have e4 : (8 * N - 6) / 2 = 4 * N - 3 := by omega
    have hP2 : Q ++ [d] ++ List.replicate (s + 4) RB.Y
        = (Q ++ [d] ++ List.replicate (s + 3) RB.Y) ++ [RB.Y] := by
      rw [List.replicate_succ']; simp
    rw [e4] at hr4 he4
    rw [hP2] at he4
    obtain ⟨hr5, he5⟩ := scan_Y_odd (b4 := b4_0LB) (u := Q ++ [d] ++ List.replicate (s + 3) RB.Y)
      (n := 4 * N - 3) (j := 2 + t + (s + 3) + 1) (by omega) he4
    rw [← hP2] at hr5
    have e5 : (4 * N - 3 - 1) / 2 = 2 * N - 2 := by omega
    have hP1 : Q ++ [d] ++ List.replicate (s + 3) RB.Y
        = (Q ++ [d] ++ List.replicate (s + 2) RB.Y) ++ [RB.Y] := by
      rw [List.replicate_succ']; simp
    rw [e5] at hr5 he5
    rw [hP1] at he5
    obtain ⟨hcfg, he6⟩ := scan_Y_even (u := Q ++ [d] ++ List.replicate (s + 2) RB.Y)
      (n := 2 * N - 2) (j := 2 + t + (s + 3) + 1 + 1) (by omega) he5
    rw [← hP1] at hcfg
    have e6 : (2 * N - 2) / 2 = N - 1 := by omega
    rw [hcfg, e6] at hr5
    rw [e6] at he6
    set v' := qw v 7 ++ [d] ++ List.replicate (s + 2) RB.Y with hv'
    have hw' : Q ++ [d] ++ List.replicate (s + 2) RB.Y = [RB.Y, RB.Y, RB.Y] ++ v' := by
      rw [hQv, hv']; simp [List.append_assoc]
    have hv'd : Digs v' := (hq7d.append (Digs.cons hdd Digs.nil)).append
      (digs_replicate (Or.inl rfl) _)
    have hv'dy : DyckPre v' := hD1.append (dyckPre_replicate_Y _)
    have hbalw : bal ([RB.Y, RB.Y, RB.Y] ++ v') = (h : ℤ) + s + 1 := by
      rw [bal_append, hv', bal_append, hbD1, bal_replicate_Y]
      simp
      ring
    have hwd' : Digs ([RB.Y, RB.Y, RB.Y] ++ v') :=
      Digs.append (by intro x hx; simp at hx; rw [hx]; exact Or.inl rfl) hv'd
    have hhtw : 6 ≤ ht ([RB.Y, RB.Y, RB.Y] ++ v') := by
      have := bal_le_ht hwd'
      omega
    -- the counter at the new checkpoint
    have hbc := buffer_counter hh5 hB htle hn1' hdXV
    have hrr : rrun ([RB.Y, RB.Y, RB.Y] ++ v') 0 = 2 ^ (s + 2) * (rstep d b + 1) - 1 := by
      rw [← hw', rrun_append, rrun_append, rrun_replicate_Y, hQ, ← trun_eq_rrun_qw]
      rfl
    have hcnt : ((N - 1 : ℕ) : ℤ) + 2 ≤ rrun ([RB.Y, RB.Y, RB.Y] ++ v') 0 := by
      rw [hrr]
      exact counter_close hN hbc
    refine ⟨[RB.Y, RB.Y, RB.Y] ++ v', N - 1, 2 + t + (s + 3) + 1 + 1,
      (4 + (k1 + (1 + (k2 + 2)))) + (kt + 6) + (T + (k3 + (6 + 6))), by omega, ?_, ?_⟩
    · rw [← hw']
      exact hrun0.trans (hrS.trans (hr3.trans (hr4.trans hr5)))
    · exact ⟨hwd', ⟨v', rfl, hv'dy⟩, by rw [← hw']; exact he6, hcnt,
        height_close hv'd hv'dy (by rw [hbalw]; omega) hhtw, by omega⟩

end BB25.Prefix
