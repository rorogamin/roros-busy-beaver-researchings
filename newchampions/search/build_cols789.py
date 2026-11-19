"""Generate exact, axiom-free Lean 4 and Rocq 9.1 proofs for ALL 9 champions in Columns m=7,8,9:
   BB(9,7), BB(10,7), BB(11,7), BB(9,8), BB(10,8), BB(11,8), BB(9,9), BB(10,9), BB(11,9).
"""
import json
from search.gen_tm import gen_lean_tm, gen_rocq_tm

with open('search/boots_9to11.json') as f:
    BOOTS = json.load(f)

COL_SPECS = {
    7: dict(
        core_type='Fwp2_H6Core',
        lean_core_proof=(
            "  ⟨⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,\n"
            "     rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,\n"
            "    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,\n"
            "   rfl, rfl, rfl⟩"
        ),
        rocq_core_proof="Proof. constructor; [constructor; [constructor; [constructor; reflexivity | ..]; reflexivity | ..]; reflexivity | ..]; reflexivity. Qed.",
        fp_lean="{c}.fh.fp",
        fp_rocq="(fh_fp _ (h6_fh _ {c}))",
        low_sym=6, low_H='H_plus2', low_ord=1, low_rep='rule_6_H_rep', low_rep_conj=True,
        min_r=1, mark=4, s1=2, s2=3, s3=4, top11=6, e1=3, e2=6, e3=5,
    ),
    8: dict(
        core_type='Fwp2_H7Core',
        lean_core_proof=(
            "  ⟨⟨⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,\n"
            "      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,\n"
            "     rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,\n"
            "    rfl, rfl, rfl⟩,\n"
            "   rfl, rfl, rfl, rfl, rfl, rfl⟩"
        ),
        rocq_core_proof="Proof. constructor; [constructor; [constructor; [constructor; [constructor; reflexivity | ..]; reflexivity | ..]; reflexivity | ..]; reflexivity | ..]; reflexivity. Qed.",
        fp_lean="{c}.h6.fh.fp",
        fp_rocq="(fh_fp _ (h6_fh _ (h7_h6 _ {c})))",
        low_sym=7, low_H='H7_H', low_ord=2, low_rep='rule_7_H_rep', low_rep_conj=False,
        min_r=2, mark=6, s1=2, s2=4, s3=5, top11=7, e1=4, e2=5, e3=7,
    ),
    9: dict(
        core_type='Fwp2_H8Core',
        lean_core_proof=(
            "  ⟨⟨⟨⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,\n"
            "       rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,\n"
            "      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,\n"
            "     rfl, rfl, rfl⟩,\n"
            "    rfl, rfl, rfl, rfl, rfl, rfl⟩,\n"
            "   rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩"
        ),
        rocq_core_proof="Proof. constructor; [constructor; [constructor; [constructor; [constructor; [constructor; reflexivity | ..]; reflexivity | ..]; reflexivity | ..]; reflexivity | ..]; reflexivity | ..]; reflexivity. Qed.",
        fp_lean="{c}.h7.h6.fh.fp",
        fp_rocq="(fh_fp _ (h6_fh _ (h7_h6 _ (h8_h7 _ {c}))))",
        low_sym=8, low_H='H8_H', low_ord=3, low_rep='rule_8_H_rep', low_rep_conj=False,
        min_r=2, mark=6, s1=2, s2=3, s3=4, top11=7, e1=4, e2=5, e3=7,
    ),
}

DOM_INFO = {
    'BB9_7':  (9, 7, 3, 7, 'BB(8, 7) > f_{ω^2+2}(8), BB(9, 6) > f_{ω^2+2}(7)'),
    'BB10_7': (10, 7, 4, 4, 'BB(9, 7) > f_{ω^2+3}(7), BB(10, 6) > f_{ω^2+3}(7)'),
    'BB11_7': (11, 7, 5, 7, 'BB(10, 7) > f_{ω^2+4}(4), BB(11, 6) > f_{ω^2+4}(8)'),
    'BB9_8':  (9, 8, 4, 7, 'BB(8, 8) > f_{ω^2+3}(7), BB(9, 7) > f_{ω^2+3}(7)'),
    'BB10_8': (10, 8, 5, 7, 'BB(9, 8) > f_{ω^2+4}(7), BB(10, 7) > f_{ω^2+4}(4)'),
    'BB11_8': (11, 8, 6, 10, 'BB(10, 8) > f_{ω^2+5}(7), BB(11, 7) > f_{ω^2+5}(7)'),
    'BB9_9':  (9, 9, 5, 7, 'BB(8, 9) > f_{ω^2+4}(7), BB(9, 8) > f_{ω^2+4}(7)'),
    'BB10_9': (10, 9, 6, 7, 'BB(9, 9) > f_{ω^2+5}(7), BB(10, 8) > f_{ω^2+5}(7)'),
    'BB11_9': (11, 9, 7, 7, 'BB(10, 9) > f_{ω^2+6}(7), BB(11, 8) > f_{ω^2+6}(10)'),
}


def gen_lean_machine(name):
    ns, ms, final_ord, final_k, prev_str = DOM_INFO[name]
    b = BOOTS[name]
    cs = COL_SPECS[ms]
    tm_id = name.lower().replace('_', '')
    core_id = f'{tm_id}_core'
    tm_str = b['tm']
    min_r = cs['min_r']
    mark = cs['mark']
    markp = mark - 1
    low = cs['low_sym']
    lowp = low - 1
    lowH = cs['low_H']
    lowOrd = cs['low_ord']
    sw = 8 if ns == 9 else 9
    r_arg = 'r' if min_r == 1 else '(r + 1)'
    low_ge17 = f'(fun z _ => {lowH}_ge_17 z)' if lowH == 'H_plus2' else f'{lowH}_ge_17'
    low_ht_proj = '(ht2 (by omega)).1' if cs['low_rep_conj'] else '(ht2 (by omega))'
    fp_expr = cs['fp_lean'].format(c=core_id)
    thm_name = f'{tm_id}_halts_gt_f_omega2_plus_{final_ord}_{final_k}'

    parts = []
    parts.append(f"""/-
  BB/{name}.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB({ns}, {ms}):
    TM: {tm_str}
    Domain: BB({ns}, {ms}) ({ns} states, {ms} symbols)
    Previous best dominated bounds: {prev_str}
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+{final_ord}}}({final_k})
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_H
import BB.Fwp2_H8

namespace BB
namespace {name}

{gen_lean_tm(tm_id, tm_str)}

theorem {core_id} : {cs['core_type']} {tm_id} :=
{cs['lean_core_proof']}

def H51 (m : Nat) : Nat := iter {lowH} (2 * m - 1) 1

theorem H51_mono {{x y : Nat}} (hxy : x ≤ y) : H51 x ≤ H51 y :=
  iter_mono_steps {lowH} (fun z => by
    cases z with | zero => exact Nat.zero_le _ | succ z' => exact Nat.le_trans (Nat.le_succ _) ({lowH}_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 1

theorem H51_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus {lowOrd + 1} m < H51 m :=
  climb_2m_minus_1 {lowH} (f_omega2_plus {lowOrd}) 1 (by omega) (fun _ _ h => {lowH}_mono h) {lowH}_inc {lowH}_gt
    (fOmega2_props 1 0 {lowOrd}) m hm

theorem H51_inc (m : Nat) (hm : 1 ≤ m) : m + 1 ≤ H51 m := by
  have h1 := H51_gt m hm; have h2 : m ≤ f_omega2_plus {lowOrd + 1} m := (fOmega2_props 1 0 {lowOrd + 1}).ge_self m; omega

theorem H51_ge_17 (m : Nat) (hm : 1 ≤ m) : 17 ≤ H51 m :=
  iter_H_ge_17 {lowH} (2 * m - 1) 1 (by omega) (by omega) {lowH}_inc {low_ge17}

theorem rule_51 (r m : Nat) (R : List Nat) (hm : 1 ≤ m) :
    ∃ r' m' t, Reaches {tm_id} (Scfg (r + {min_r}) 0 m (5 :: 1 :: R)) (Scfg (r' + {min_r}) 0 m' (5 :: R)) t ∧
      H51 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_51_4step (tm := {tm_id}) (sw := {sw}) (mark' := {markp}) (low' := {lowp})
    (s1 := {cs['s1']}) (s2 := {cs['s2']}) (s3 := {cs['s3']}) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl {r_arg} m hm R
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := {cs['low_rep']} {core_id} (2 * m - 1) r 1 (5 :: R) (by omega)
  exact ⟨r2, m2, t0 + t2, reaches_trans h0 h2, hm2, Nat.le_trans {low_ht_proj} (Nat.le_add_left _ _)⟩
""")

    if ns >= 10:
        parts.append(f"""def H5mid (m : Nat) : Nat := iter H51 (2 * m + 1) 1

theorem H5mid_mono {{x y : Nat}} (hxy : x ≤ y) : H5mid x ≤ H5mid y :=
  iter_mono_steps H51 (fun z => by
    cases z with | zero => exact Nat.zero_le _ | succ z' => exact Nat.le_trans (Nat.le_succ _) (H51_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 1

theorem H5mid_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus {lowOrd + 2} m < H5mid m :=
  climb_2m_plus_1 H51 (f_omega2_plus {lowOrd + 1}) 1 (by omega) (fun _ _ h => H51_mono h) H51_inc H51_gt
    (fOmega2_props 1 0 {lowOrd + 1}) m hm

theorem H5mid_inc (m : Nat) (hm : 1 ≤ m) : m + 1 ≤ H5mid m := by
  have h1 := H5mid_gt m hm; have h2 : m ≤ f_omega2_plus {lowOrd + 2} m := (fOmega2_props 1 0 {lowOrd + 2}).ge_self m; omega

theorem H5mid_ge_17 (m : Nat) : 17 ≤ H5mid m :=
  iter_H_ge_17 H51 (2 * m + 1) 1 (by omega) (by omega) H51_inc H51_ge_17

theorem rule_5mid (r m : Nat) (R : List Nat) :
    ∃ r' m' t, Reaches {tm_id} (Scfg (r + {min_r}) 0 m (5 :: {mark} :: R)) (Scfg (r' + {min_r}) 0 m' (5 :: R)) t ∧
      H5mid m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_5mark_empty (tm := {tm_id}) (mark' := {markp}) {fp_expr}
    rfl rfl rfl rfl rfl rfl rfl rfl {r_arg} m R
  have hpe : 1 ≤ Pempty {r_arg} := Nat.le_trans (by omega) (Pempty_ge {r_arg})
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep {min_r} 1 H51
    (fun _ _ h => H51_mono h) (fun z hz => Nat.le_trans (by omega : 1 ≤ 17) (H51_ge_17 z hz))
    rule_51 (2 * m + 1) r (Pempty {r_arg}) R hpe
  have harg : H5mid m ≤ iter H51 (2 * m + 1) (Pempty {r_arg}) :=
    iter_mono_arg H51 (fun _ _ h => H51_mono h) (2 * m + 1) hpe
  exact ⟨r2, m2, t0 + t2, reaches_trans h0 h2, Nat.le_trans harg hm2,
    Nat.le_trans (ht2 (by omega)) (Nat.le_add_left _ _)⟩
""")

    if ns >= 11:
        parts.append(f"""def H5top (m : Nat) : Nat := iter H5mid (2 * m + 1) 0

theorem H5top_mono {{x y : Nat}} (hxy : x ≤ y) : H5top x ≤ H5top y :=
  iter_mono_steps H5mid (fun z => by
    cases z with | zero => exact Nat.zero_le _ | succ z' => exact Nat.le_trans (Nat.le_succ _) (H5mid_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 0

theorem H5top_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus {lowOrd + 3} m < H5top m := by
  have hsplit : iter H5mid (2 * m + 1) 0 = iter H5mid (2 * m) (H5mid 0) := by
    rw [iter_add H5mid (2 * m) 1 0, iter_succ, iter_zero]
  have h0 : 1 ≤ H5mid 0 := Nat.le_trans (by omega : 1 ≤ 17) (H5mid_ge_17 0)
  have h1 := climb_double H5mid (f_omega2_plus {lowOrd + 2}) 1 (by omega) (fun _ _ h => H5mid_mono h) H5mid_inc H5mid_gt
    (fOmega2_props 1 0 {lowOrd + 2}) m hm
  have h2 := iter_mono_arg H5mid (fun _ _ h => H5mid_mono h) (2 * m) h0
  unfold H5top; rw [hsplit]; exact Nat.lt_of_lt_of_le h1 h2

theorem H5top_ge_17 (m : Nat) : 17 ≤ H5top m := by
  unfold H5top; rw [iter_succ]; exact H5mid_ge_17 _

theorem rule_5top (r m : Nat) (R : List Nat) :
    ∃ r' m' t, Reaches {tm_id} (Scfg (r + {min_r}) 0 m (5 :: {cs['top11']} :: R)) (Scfg (r' + {min_r}) 0 m' (5 :: R)) t ∧
      H5top m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_5top_zero (tm := {tm_id}) (mark' := {markp}) (top := {cs['top11']})
    (e1 := {cs['e1']}) (e2 := {cs['e2']}) (e3 := {cs['e3']})
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl {r_arg} m R
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep0 {min_r} {mark} H5mid
    (fun _ _ h => H5mid_mono h) rule_5mid (2 * m + 1) r 0 R
  exact ⟨r2, m2, t0 + t2, reaches_trans h0 h2, hm2, Nat.le_trans (ht2 (by omega)) (Nat.le_add_left _ _)⟩
""")

    # Bootstrap & final theorem!
    r_boot = b['r']
    m_boot = b['m']
    step_boot = b['step']
    r0 = r_boot - min_r
    top_sym = b['top_sym']

    if name == 'BB11_8':
        parts.append(f"""set_option maxRecDepth 2000 in
theorem {tm_id}_bootstrap :
    Reaches {tm_id} initConfig (Scfg {r_boot} 0 {m_boot} (5 :: rep 11 7 [1])) {step_boot} := rfl

theorem {thm_name} :
    ValidTM {ns} {ms} {tm_id} ∧ ∃ t, HaltsIn {tm_id} initConfig t ∧ f_omega2_plus {final_ord} {final_k} < t := by
  refine ⟨{tm_id}_valid, ?_⟩
  have hboot := {tm_id}_bootstrap
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_5top {r0} {m_boot} (rep 10 7 [1])
  have hm1_k : {final_k} ≤ m1 := Nat.le_trans (by omega : {final_k} ≤ 17) (Nat.le_trans (H5top_ge_17 {m_boot}) hm1)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep0 {min_r} 7 H5top (fun _ _ h => H5top_mono h) rule_5top {final_k} r1 m1 [1]
  have hm2_pos : 1 ≤ m2 := by
    have h0 : 1 ≤ iter H5top 10 {final_k} := by
      have hg := iter_strict_dom H5top (f_omega2_plus {final_ord - 1}) 1 H5top_gt (fOmega2_props 1 0 {final_ord - 1}) 10 10 (by omega) (by omega)
      omega
    exact Nat.le_trans h0 (Nat.le_trans (iter_mono_arg H5top (fun _ _ h => H5top_mono h) 10 hm1_k) hm2)
  obtain ⟨r3, m3, t3, h3, _, _⟩ := rule_51 r2 m2 [] hm2_pos
  obtain ⟨cf, hhalt, hst⟩ := halt_cursor_5 (tm := {tm_id}) (mark' := {markp}) rfl rfl (r3 + {min_r}) m3
  have hreach := reaches_trans (reaches_trans (reaches_trans (reaches_trans hboot h1) h2) h3) hhalt
  have hlt1 : f_omega2_plus {final_ord} {final_k} < iter H5top {final_k} {final_k} :=
    iter_strict_dom H5top (f_omega2_plus {final_ord - 1}) 1 H5top_gt (fOmega2_props 1 0 {final_ord - 1}) {final_k} {final_k} (by omega) (by omega)
  have hlt2 : iter H5top {final_k} {final_k} ≤ iter H5top {final_k} m1 := iter_mono_arg H5top (fun _ _ h => H5top_mono h) {final_k} hm1_k
  have hlt_m2 : f_omega2_plus {final_ord} {final_k} < m2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm2
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  refine ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans hle_t (by omega))⟩
""")
    elif name == 'BB11_9':
        parts.append(f"""set_option maxRecDepth 2000 in
theorem {tm_id}_bootstrap :
    Reaches {tm_id} initConfig (Scfg {r_boot} 0 {m_boot} (1 :: 5 :: rep 8 7 [])) {step_boot} := rfl

theorem {thm_name} :
    ValidTM {ns} {ms} {tm_id} ∧ ∃ t, HaltsIn {tm_id} initConfig t ∧ f_omega2_plus {final_ord} {final_k} < t := by
  refine ⟨{tm_id}_valid, ?_⟩
  have hboot := {tm_id}_bootstrap
  obtain ⟨t0, h0, _⟩ := fwp2_step {fp_expr} {r_boot} 0 {m_boot} (5 :: rep 8 7 [])
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_5top {r0} (Pfn {r_boot} 0 {m_boot}) (rep {final_k} 7 [])
  have hm1_k : {final_k} ≤ m1 := Nat.le_trans (by omega : {final_k} ≤ 17) (Nat.le_trans (H5top_ge_17 _) hm1)
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep0 {min_r} 7 H5top (fun _ _ h => H5top_mono h) rule_5top {final_k} r1 m1 []
  obtain ⟨cf, hhalt, hst⟩ := halt_cursor_5 (tm := {tm_id}) (mark' := {markp}) rfl rfl (r2 + {min_r}) m2
  have hreach := reaches_trans (reaches_trans (reaches_trans (reaches_trans hboot h0) h1) h2) hhalt
  have hlt1 : f_omega2_plus {final_ord} {final_k} < iter H5top {final_k} {final_k} :=
    iter_strict_dom H5top (f_omega2_plus {final_ord - 1}) 1 H5top_gt (fOmega2_props 1 0 {final_ord - 1}) {final_k} {final_k} (by omega) (by omega)
  have hlt2 : iter H5top {final_k} {final_k} ≤ iter H5top {final_k} m1 := iter_mono_arg H5top (fun _ _ h => H5top_mono h) {final_k} hm1_k
  have hlt_m2 : f_omega2_plus {final_ord} {final_k} < m2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm2
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  refine ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans hle_t (by omega))⟩
""")
    else:
        n_top = b['top']
        assert n_top == final_k + 1
        if ns == 9:
            Htop, rtop = 'H51', 'rule_51'
            warmup = f"obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_51 {r0} {m_boot} (rep {final_k} {top_sym} []) (by omega)"
            hm1_proof = f"have hm1_k : {final_k} ≤ m1 := Nat.le_trans (by omega : {final_k} ≤ 17) (Nat.le_trans (H51_ge_17 {m_boot} (by omega)) hm1)"
            rep_call = (f"obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep {min_r} {top_sym} H51\n"
                        f"    (fun _ _ h => H51_mono h) (fun z hz => Nat.le_trans (by omega : 1 ≤ 17) (H51_ge_17 z hz))\n"
                        f"    rule_51 {final_k} r1 m1 [] (by omega)")
        elif ns == 10:
            Htop, rtop = 'H5mid', 'rule_5mid'
            warmup = f"obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_5mid {r0} {m_boot} (rep {final_k} {top_sym} [])"
            hm1_proof = f"have hm1_k : {final_k} ≤ m1 := Nat.le_trans (by omega : {final_k} ≤ 17) (Nat.le_trans (H5mid_ge_17 {m_boot}) hm1)"
            rep_call = f"obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep0 {min_r} {top_sym} H5mid (fun _ _ h => H5mid_mono h) rule_5mid {final_k} r1 m1 []"
        else:
            Htop, rtop = 'H5top', 'rule_5top'
            warmup = f"obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_5top {r0} {m_boot} (rep {final_k} {top_sym} [])"
            hm1_proof = f"have hm1_k : {final_k} ≤ m1 := Nat.le_trans (by omega : {final_k} ≤ 17) (Nat.le_trans (H5top_ge_17 {m_boot}) hm1)"
            rep_call = f"obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := iter_cursor_rep0 {min_r} {top_sym} H5top (fun _ _ h => H5top_mono h) rule_5top {final_k} r1 m1 []"

        parts.append(f"""set_option maxRecDepth 2000 in
theorem {tm_id}_bootstrap :
    Reaches {tm_id} initConfig (Scfg {r_boot} 0 {m_boot} (5 :: rep {n_top} {top_sym} [])) {step_boot} := rfl

theorem {thm_name} :
    ValidTM {ns} {ms} {tm_id} ∧ ∃ t, HaltsIn {tm_id} initConfig t ∧ f_omega2_plus {final_ord} {final_k} < t := by
  refine ⟨{tm_id}_valid, ?_⟩
  have hboot := {tm_id}_bootstrap
  {warmup}
  {hm1_proof}
  {rep_call}
  obtain ⟨cf, hhalt, hst⟩ := halt_cursor_5 (tm := {tm_id}) (mark' := {markp}) rfl rfl (r2 + {min_r}) m2
  have hreach := reaches_trans (reaches_trans (reaches_trans hboot h1) h2) hhalt
  have hlt1 : f_omega2_plus {final_ord} {final_k} < iter {Htop} {final_k} {final_k} :=
    iter_strict_dom {Htop} (f_omega2_plus {final_ord - 1}) 1 {Htop}_gt (fOmega2_props 1 0 {final_ord - 1}) {final_k} {final_k} (by omega) (by omega)
  have hlt2 : iter {Htop} {final_k} {final_k} ≤ iter {Htop} {final_k} m1 := iter_mono_arg {Htop} (fun _ _ h => {Htop}_mono h) {final_k} hm1_k
  have hlt_m2 : f_omega2_plus {final_ord} {final_k} < m2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm2
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  refine ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans hle_t (by omega))⟩
""")

    parts.append(f"""#print axioms {thm_name}

end {name}
end BB
""")
    return '\n'.join(parts)


def gen_rocq_machine(name):
    ns, ms, final_ord, final_k, prev_str = DOM_INFO[name]
    b = BOOTS[name]
    cs = COL_SPECS[ms]
    tm_id = name.lower().replace('_', '')
    core_id = f'{tm_id}_core'
    tm_str = b['tm']
    min_r = cs['min_r']
    mark = cs['mark']
    markp = mark - 1
    low = cs['low_sym']
    lowp = low - 1
    lowH = cs['low_H']
    lowOrd = cs['low_ord']
    sw = 8 if ns == 9 else 9
    r_arg = 'r' if min_r == 1 else '(S r)'
    r_scfg = 'S r' if min_r == 1 else 'S (S r)'
    r_scfg_p = "S r2" if min_r == 1 else "S (S r2)"
    low_ge17 = f'(fun z _ => {lowH}_ge_17 z)' if lowH == 'H_plus2' else f'{lowH}_ge_17'
    low_ht_destruct = 'destruct (Ht2 ltac:(lia)) as [Ht2a _]; lia' if cs['low_rep_conj'] else 'pose proof (Ht2 ltac:(lia)); lia'
    fp_expr = cs['fp_rocq'].format(c=core_id)
    thm_name = f'{tm_id}_halts_gt_f_omega2_plus_{final_ord}_{final_k}'

    parts = []
    parts.append(f"""(*
  rocq/{name}.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB({ns}, {ms}):
    TM: {tm_str}
    Domain: BB({ns}, {ms}) ({ns} states, {ms} symbols)
    Previous best dominated bounds: {prev_str}
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+{final_ord}}}({final_k})
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_H Fwp2_H8.
Import ListNotations.

{gen_rocq_tm(tm_id, tm_str)}

Lemma {core_id} : {cs['core_type']} {tm_id}.
{cs['rocq_core_proof']}

Definition H51 (m : nat) : nat := iter {lowH} (2 * m - 1) 1.

Lemma H51_mono : forall x y, x <= y -> H51 x <= H51 y.
Proof.
  intros x y Hxy. unfold H51.
  apply iter_mono_steps; [intro z; destruct z; [lia | pose proof ({lowH}_inc (S z) ltac:(lia)); lia] | lia].
Qed.

Lemma H51_gt : forall m, 1 <= m -> f_omega2_plus {lowOrd + 1} m < H51 m.
Proof.
  intros m Hm. unfold H51.
  apply (climb_2m_minus_1 {lowH} (f_omega2_plus {lowOrd}) 1 ltac:(lia) {lowH}_mono {lowH}_inc {lowH}_gt (fOmega2_props 1 0 {lowOrd}) m Hm).
Qed.

Lemma H51_inc : forall m, 1 <= m -> S m <= H51 m.
Proof.
  intros m Hm. pose proof (H51_gt m Hm).
  pose proof (fgh_ge_self _ (fOmega2_props 1 0 {lowOrd + 1}) m).
  change (f_omega2_plus {lowOrd + 1} m) with (fOmega2 1 0 {lowOrd + 1} m) in *. lia.
Qed.

Lemma H51_ge_17 : forall m, 1 <= m -> 17 <= H51 m.
Proof.
  intros m Hm. unfold H51.
  apply (iter_H_ge_17 {lowH} (2 * m - 1) 1 ltac:(lia) ltac:(lia) {lowH}_inc {low_ge17}).
Qed.

Lemma rule_51 : forall r m R, 1 <= m ->
  exists r' m' t, Reaches {tm_id} (Scfg (r + {min_r}) 0 m (5 :: 1 :: R)) (Scfg (r' + {min_r}) 0 m' (5 :: R)) t /\\
    H51 m <= m' /\\ m' <= t.
Proof.
  intros r m R Hm.
  destruct (reload_51_4step {tm_id} {sw} {markp} {lowp} {cs['s1']} {cs['s2']} {cs['s3']} {r_arg} m R
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hm) as [t0 H0].
  destruct ({cs['low_rep']} {tm_id} {core_id} (2 * m - 1) r 1 (5 :: R) ltac:(lia)) as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  exists r2, m2, (t0 + t2).
  replace (r + {min_r}) with ({r_scfg}) by lia.
  replace (r2 + {min_r}) with ({r_scfg_p}) by lia.
  split; [eapply reaches_trans; eassumption | split; [exact Hm2 | {low_ht_destruct}]].
Qed.
""")

    if ns >= 10:
        parts.append(f"""Definition H5mid (m : nat) : nat := iter H51 (2 * m + 1) 1.

Lemma H5mid_mono : forall x y, x <= y -> H5mid x <= H5mid y.
Proof.
  intros x y Hxy. unfold H5mid.
  apply iter_mono_steps; [intro z; destruct z; [lia | pose proof (H51_inc (S z) ltac:(lia)); lia] | lia].
Qed.

Lemma H5mid_gt : forall m, 1 <= m -> f_omega2_plus {lowOrd + 2} m < H5mid m.
Proof.
  intros m Hm. unfold H5mid.
  apply (climb_2m_plus_1 H51 (f_omega2_plus {lowOrd + 1}) 1 ltac:(lia) H51_mono H51_inc H51_gt (fOmega2_props 1 0 {lowOrd + 1}) m Hm).
Qed.

Lemma H5mid_inc : forall m, 1 <= m -> S m <= H5mid m.
Proof.
  intros m Hm. pose proof (H5mid_gt m Hm).
  pose proof (fgh_ge_self _ (fOmega2_props 1 0 {lowOrd + 2}) m).
  change (f_omega2_plus {lowOrd + 2} m) with (fOmega2 1 0 {lowOrd + 2} m) in *. lia.
Qed.

Lemma H5mid_ge_17 : forall m, 17 <= H5mid m.
Proof.
  intro m. unfold H5mid.
  apply (iter_H_ge_17 H51 (2 * m + 1) 1 ltac:(lia) ltac:(lia) H51_inc H51_ge_17).
Qed.

Lemma rule_5mid : forall r m R,
  exists r' m' t, Reaches {tm_id} (Scfg (r + {min_r}) 0 m (5 :: {mark} :: R)) (Scfg (r' + {min_r}) 0 m' (5 :: R)) t /\\
    H5mid m <= m' /\\ m' <= t.
Proof.
  intros r m R.
  destruct (reload_5mark_empty {tm_id} {markp} {fp_expr} {r_arg} m R
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as [t0 H0].
  assert (Hpe : 1 <= Pempty {r_arg}) by (pose proof (Pempty_ge {r_arg}); lia).
  assert (Hpos : forall x, 1 <= x -> 1 <= H51 x) by (intros x Hx; pose proof (H51_ge_17 x Hx); lia).
  destruct (iter_cursor_rep {tm_id} {min_r} 1 H51 H51_mono Hpos rule_51 (2 * m + 1) r (Pempty {r_arg}) R Hpe)
    as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  exists r2, m2, (t0 + t2).
  replace ({r_scfg}) with (r + {min_r}) in H0 by lia.
  split; [eapply reaches_trans; eassumption | split].
  - unfold H5mid. eapply Nat.le_trans; [apply iter_mono_arg; [apply H51_mono | exact Hpe] | exact Hm2].
  - pose proof (Ht2 ltac:(lia)). lia.
Qed.
""")

    if ns >= 11:
        parts.append(f"""Definition H5top (m : nat) : nat := iter H5mid (2 * m + 1) 0.

Lemma H5top_mono : forall x y, x <= y -> H5top x <= H5top y.
Proof.
  intros x y Hxy. unfold H5top.
  apply iter_mono_steps; [intro z; destruct z; [lia | pose proof (H5mid_inc (S z) ltac:(lia)); lia] | lia].
Qed.

Lemma H5top_gt : forall m, 1 <= m -> f_omega2_plus {lowOrd + 3} m < H5top m.
Proof.
  intros m Hm. unfold H5top.
  rewrite iter_add, iter_succ, iter_zero.
  assert (H0 : 1 <= H5mid 0) by (pose proof (H5mid_ge_17 0); lia).
  pose proof (climb_double H5mid (f_omega2_plus {lowOrd + 2}) 1 ltac:(lia) H5mid_mono H5mid_inc H5mid_gt (fOmega2_props 1 0 {lowOrd + 2}) m Hm) as H1.
  pose proof (iter_mono_arg H5mid H5mid_mono (2 * m) 1 (H5mid 0) H0) as H2.
  change (f_omega2_plus {lowOrd + 3} m) with (fNext (f_omega2_plus {lowOrd + 2}) m). lia.
Qed.

Lemma H5top_ge_17 : forall m, 17 <= H5top m.
Proof.
  intro m. unfold H5top.
  replace (2 * m + 1) with (S (2 * m)) by lia. rewrite iter_succ. apply H5mid_ge_17.
Qed.

Lemma rule_5top : forall r m R,
  exists r' m' t, Reaches {tm_id} (Scfg (r + {min_r}) 0 m (5 :: {cs['top11']} :: R)) (Scfg (r' + {min_r}) 0 m' (5 :: R)) t /\\
    H5top m <= m' /\\ m' <= t.
Proof.
  intros r m R.
  destruct (reload_5top_zero {tm_id} {markp} {cs['top11']} {cs['e1']} {cs['e2']} {cs['e3']} {r_arg} m R
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as [t0 H0].
  destruct (iter_cursor_rep0 {tm_id} {min_r} {mark} H5mid H5mid_mono rule_5mid (2 * m + 1) r 0 R)
    as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  exists r2, m2, (t0 + t2).
  replace ({r_scfg}) with (r + {min_r}) in H0 by lia.
  split; [eapply reaches_trans; eassumption | split; [exact Hm2 | pose proof (Ht2 ltac:(lia)); lia]].
Qed.
""")

    r_boot = b['r']
    m_boot = b['m']
    step_boot = b['step']
    r0 = r_boot - min_r
    top_sym = b['top_sym']

    if name == 'BB11_8':
        parts.append(f"""Lemma {tm_id}_bootstrap :
  Reaches {tm_id} initConfig (Scfg {r_boot} 0 {m_boot} (5 :: rep 11 7 [1])) {step_boot}.
Proof. vm_compute. reflexivity. Qed.

Theorem {thm_name} :
  ValidTM {ns} {ms} {tm_id} /\\ exists t, HaltsIn {tm_id} initConfig t /\\ f_omega2_plus {final_ord} {final_k} < t.
Proof.
  split; [exact {tm_id}_valid |].
  pose proof {tm_id}_bootstrap as Hboot.
  destruct (rule_5top {r0} {m_boot} (rep 10 7 [1])) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
  assert (Hm1_k : {final_k} <= m1) by (pose proof (H5top_ge_17 {m_boot}); lia).
  destruct (iter_cursor_rep0 {tm_id} {min_r} 7 H5top H5top_mono rule_5top {final_k} r1 m1 [1])
    as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  pose proof (iter_strict_dom H5top (f_omega2_plus {final_ord - 1}) 1 H5top_gt (fOmega2_props 1 0 {final_ord - 1}) {final_k} {final_k} ltac:(lia) ltac:(lia)) as Hlt1.
  pose proof (iter_mono_arg H5top H5top_mono {final_k} {final_k} m1 Hm1_k) as Hlt2.
  destruct (rule_51 r2 m2 [] ltac:(lia)) as [r3 [m3 [t3 [H3 _]]]].
  destruct (halt_cursor_5 {tm_id} {markp} (r3 + {min_r}) m3 eq_refl eq_refl) as [cf [Hhalt Hst]].
  pose proof (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ Hboot H1) H2) H3) Hhalt) as Hreach.
  pose proof (Ht2 ltac:(lia)) as Hlet.
  eexists. split; [eexists; split; [exact Hreach | exact Hst] |].
  change (f_omega2_plus {final_ord} {final_k}) with (iter (f_omega2_plus {final_ord - 1}) {final_k} {final_k}). lia.
Qed.
""")
    elif name == 'BB11_9':
        parts.append(f"""Lemma {tm_id}_bootstrap :
  Reaches {tm_id} initConfig (Scfg {r_boot} 0 {m_boot} (1 :: 5 :: rep 8 7 [])) {step_boot}.
Proof. vm_compute. reflexivity. Qed.

Theorem {thm_name} :
  ValidTM {ns} {ms} {tm_id} /\\ exists t, HaltsIn {tm_id} initConfig t /\\ f_omega2_plus {final_ord} {final_k} < t.
Proof.
  split; [exact {tm_id}_valid |].
  pose proof {tm_id}_bootstrap as Hboot.
  destruct (fwp2_step {tm_id} {fp_expr} {r_boot} 0 {m_boot} (5 :: rep 8 7 [])) as [t0 [H0 _]].
  destruct (rule_5top {r0} (Pfn {r_boot} 0 {m_boot}) (rep {final_k} 7 [])) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
  assert (Hm1_k : {final_k} <= m1) by (pose proof (H5top_ge_17 (Pfn {r_boot} 0 {m_boot})); lia).
  destruct (iter_cursor_rep0 {tm_id} {min_r} 7 H5top H5top_mono rule_5top {final_k} r1 m1 [])
    as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  destruct (halt_cursor_5 {tm_id} {markp} (r2 + {min_r}) m2 eq_refl eq_refl) as [cf [Hhalt Hst]].
  pose proof (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ Hboot H0) H1) H2) Hhalt) as Hreach.
  pose proof (iter_strict_dom H5top (f_omega2_plus {final_ord - 1}) 1 H5top_gt (fOmega2_props 1 0 {final_ord - 1}) {final_k} {final_k} ltac:(lia) ltac:(lia)) as Hlt1.
  pose proof (iter_mono_arg H5top H5top_mono {final_k} {final_k} m1 Hm1_k) as Hlt2.
  pose proof (Ht2 ltac:(lia)) as Hlet.
  eexists. split; [eexists; split; [exact Hreach | exact Hst] |].
  change (f_omega2_plus {final_ord} {final_k}) with (iter (f_omega2_plus {final_ord - 1}) {final_k} {final_k}). lia.
Qed.
""")
    else:
        n_top = b['top']
        if ns == 9:
            Htop = 'H51'
            warmup = f"destruct (rule_51 {r0} {m_boot} (rep {final_k} {top_sym} []) ltac:(lia)) as [r1 [m1 [t1 [H1 [Hm1 _]]]]]."
            hm1_proof = f"assert (Hm1_k : {final_k} <= m1) by (pose proof (H51_ge_17 {m_boot} ltac:(lia)); lia)."
            rep_call = (f"assert (Hpos : forall x, 1 <= x -> 1 <= H51 x) by (intros x Hx; pose proof (H51_ge_17 x Hx); lia).\n"
                        f"  destruct (iter_cursor_rep {tm_id} {min_r} {top_sym} H51 H51_mono Hpos rule_51 {final_k} r1 m1 [] ltac:(lia))\n"
                        f"    as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].")
        elif ns == 10:
            Htop = 'H5mid'
            warmup = f"destruct (rule_5mid {r0} {m_boot} (rep {final_k} {top_sym} [])) as [r1 [m1 [t1 [H1 [Hm1 _]]]]]."
            hm1_proof = f"assert (Hm1_k : {final_k} <= m1) by (pose proof (H5mid_ge_17 {m_boot}); lia)."
            rep_call = (f"destruct (iter_cursor_rep0 {tm_id} {min_r} {top_sym} H5mid H5mid_mono rule_5mid {final_k} r1 m1 [])\n"
                        f"    as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].")
        else:
            Htop = 'H5top'
            warmup = f"destruct (rule_5top {r0} {m_boot} (rep {final_k} {top_sym} [])) as [r1 [m1 [t1 [H1 [Hm1 _]]]]]."
            hm1_proof = f"assert (Hm1_k : {final_k} <= m1) by (pose proof (H5top_ge_17 {m_boot}); lia)."
            rep_call = (f"destruct (iter_cursor_rep0 {tm_id} {min_r} {top_sym} H5top H5top_mono rule_5top {final_k} r1 m1 [])\n"
                        f"    as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].")

        parts.append(f"""Lemma {tm_id}_bootstrap :
  Reaches {tm_id} initConfig (Scfg {r_boot} 0 {m_boot} (5 :: rep {n_top} {top_sym} [])) {step_boot}.
Proof. vm_compute. reflexivity. Qed.

Theorem {thm_name} :
  ValidTM {ns} {ms} {tm_id} /\\ exists t, HaltsIn {tm_id} initConfig t /\\ f_omega2_plus {final_ord} {final_k} < t.
Proof.
  split; [exact {tm_id}_valid |].
  pose proof {tm_id}_bootstrap as Hboot.
  {warmup}
  {hm1_proof}
  {rep_call}
  destruct (halt_cursor_5 {tm_id} {markp} (r2 + {min_r}) m2 eq_refl eq_refl) as [cf [Hhalt Hst]].
  pose proof (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ Hboot H1) H2) Hhalt) as Hreach.
  pose proof (iter_strict_dom {Htop} (f_omega2_plus {final_ord - 1}) 1 {Htop}_gt (fOmega2_props 1 0 {final_ord - 1}) {final_k} {final_k} ltac:(lia) ltac:(lia)) as Hlt1.
  pose proof (iter_mono_arg {Htop} {Htop}_mono {final_k} {final_k} m1 Hm1_k) as Hlt2.
  pose proof (Ht2 ltac:(lia)) as Hlet.
  eexists. split; [eexists; split; [exact Hreach | exact Hst] |].
  change (f_omega2_plus {final_ord} {final_k}) with (iter (f_omega2_plus {final_ord - 1}) {final_k} {final_k}). lia.
Qed.
""")

    parts.append(f"Print Assumptions {thm_name}.\n")
    return '\n'.join(parts)


if __name__ == '__main__':
    for name in DOM_INFO:
        lp = f'lean/BB/{name}.lean'
        rp = f'rocq/{name}.v'
        with open(lp, 'w', encoding='utf-8') as f:
            f.write(gen_lean_machine(name))
        with open(rp, 'w', encoding='utf-8') as f:
            f.write(gen_rocq_machine(name))
        print(f"Wrote {lp} and {rp}")
