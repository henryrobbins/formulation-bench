import Common
import problems.p12.formulations.a.Formulation
import problems.p12.formulations.d.Formulation
import Mathlib.Tactic

open BigOperators Finset

namespace P12

-- ============================================================================
-- § Parameter Mapping
-- ============================================================================

/-- The identity parameter mapping from formulation `a` to formulation `d`.
The two parameter types are structurally identical but distinct, so the
identity has to be written out field by field. -/
def paramMapAD (p : P12.a.Params) : P12.d.Params :=
  { n  := p.n
    c  := p.c
    hn := p.hn }

-- ============================================================================
-- § Witness Instance
-- ============================================================================

/-- The degenerate 3-city instance used as the witness (source side). -/
private abbrev p3 : P12.a.Params :=
  ⟨3, fun _ _ => 0, by norm_num⟩

/-- The same instance on the target side (`= paramMapAD p3`, definitionally). -/
private abbrev q3 : P12.d.Params :=
  ⟨3, fun _ _ => 0, by norm_num⟩

/-- The tour `0 → 1 → 2 → 0`, feasible for formulation `a` at `p3`. -/
private def tour3 : P12.a.Vars p3 :=
  { x := fun i j => if j.val = (i.val + 1) % 3 then 1 else 0
    u := fun i => (i.val : ℝ) + 1 }

private lemma tour3_feasible : P12.a.Feasible p3 tour3 := by
  refine
    { hout := ?_, hin := ?_, hmtz := ?_, hu_depot := ?_, hx_bin := ?_,
      hu_lo := ?_, hu_hi := ?_, hx_no_self := ?_ }
  · intro i; fin_cases i <;> rw [Fin.sum_univ_three] <;> simp [tour3]
  · intro j; fin_cases j <;> rw [Fin.sum_univ_three] <;> simp [tour3]
  · intro i j hi hj hij; fin_cases i <;> fin_cases j <;> simp_all [tour3] <;> norm_num
  · simp [tour3]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [tour3]
  · intro i hi; fin_cases i
    · exact absurd rfl hi
    · norm_num [tour3]
    · norm_num [tour3]
  · intro i; fin_cases i <;> norm_num [tour3]
  · intro i; fin_cases i <;> simp [tour3]

/-- Any point feasible for formulation `d` at the 3-city instance is impossible.
The degree, binary, and no-self-loop constraints force `x` to be a 3-cycle, so
exactly one of the non-depot arcs `1 → 2`, `2 → 1` is active. On the active arc
`i → j`, the MTZ constraint gives `u j - u i ≥ 1`, while the EC3 cut (whose
right-hand side collapses to `0` there) gives `u j - u i ≤ 0` — a contradiction.
Hence the `d`-feasible set at this instance is empty. -/
private lemma d_infeasible (w : P12.d.Vars q3)
    (h : P12.d.Feasible q3 w) : False := by
  have ho0 := h.hout 0; have ho1 := h.hout 1; have ho2 := h.hout 2
  have hi0 := h.hin 0; have hi1 := h.hin 1; have hi2 := h.hin 2
  rw [Fin.sum_univ_three] at ho0 ho1 ho2 hi0 hi1 hi2
  have s00 := h.hx_no_self 0; have s11 := h.hx_no_self 1; have s22 := h.hx_no_self 2
  -- On each non-depot arc the MTZ and EC3 constraints, specialised to `n = 3`.
  have hmtz12 := h.hmtz 1 2 (by decide) (by decide) (by decide)
  have hmtz21 := h.hmtz 2 1 (by decide) (by decide) (by decide)
  have hec12 := h.hec3 1 2 (by decide) (by decide) (by decide)
  have hec21 := h.hec3 2 1 (by decide) (by decide) (by decide)
  push_cast at hmtz12 hmtz21 hec12 hec21
  -- Split on which non-depot arc is active.
  rcases h.hx_bin 1 2 with h12 | h12 <;> rcases h.hx_bin 2 1 with h21 | h21
  · -- both inactive: contradicts the degree constraints
    omega
  · -- arc 2 → 1 active
    have e01 : w.x 0 1 = 0 := by omega
    have e10 : w.x 1 0 = 1 := by omega
    have e02 : w.x 0 2 = 1 := by omega
    have c12 : (w.x 1 2 : ℝ) = 0 := by exact_mod_cast h12
    have c21 : (w.x 2 1 : ℝ) = 1 := by exact_mod_cast h21
    have c10 : (w.x 1 0 : ℝ) = 1 := by exact_mod_cast e10
    have c02 : (w.x 0 2 : ℝ) = 1 := by exact_mod_cast e02
    rw [c21] at hmtz21
    rw [c10, c12, c02, c21] at hec21
    linarith
  · -- arc 1 → 2 active
    have e01 : w.x 0 1 = 1 := by omega
    have e20 : w.x 2 0 = 1 := by omega
    have c12 : (w.x 1 2 : ℝ) = 1 := by exact_mod_cast h12
    have c21 : (w.x 2 1 : ℝ) = 0 := by exact_mod_cast h21
    have c20 : (w.x 2 0 : ℝ) = 1 := by exact_mod_cast e20
    have c01 : (w.x 0 1 : ℝ) = 1 := by exact_mod_cast e01
    rw [c12] at hmtz12
    rw [c20, c21, c01, c12] at hec12
    linarith
  · -- both active: contradicts the degree constraints
    omega

-- ============================================================================
-- § Disproof
-- ============================================================================

/-- Formulation `d` (MTZ augmented with the EC3 cut) is **not** a reformulation
of formulation `a` (MTZ) under the identity parameter mapping: no
`MILPReformulation` whose `paramMap` is `paramMapAD` can exist.

Witness: the 3-city instance. The `a`-feasible set consists of the two tours
`0 → 1 → 2 → 0` and `0 → 2 → 1 → 0`. Both violate the EC3 cut, so the
`d`-feasible set at this instance is empty. Pushing the `a`-feasible tour
`0 → 1 → 2 → 0` through `Φ.fwd` therefore lands in the empty `d`-feasible set —
a contradiction. This is the constructive form of the cardinality obstruction
`MILPReformulation.fwd_injOn`.

Pinning the parameter mapping is necessary: EC3 is valid on every instance with
`n ≥ 4`, so an unrestricted parameter mapping is free to redirect the two
degenerate sizes `n ∈ {2, 3}` to 4-city instances on which the cut is inert,
and a reformulation does then exist. -/
theorem not_aDReformulation
    (Φ : MILPReformulation P12.a.formulation P12.d.formulation)
    (hΦ : Φ.paramMap = paramMapAD) : False := by
  obtain ⟨paramMap, fwd, _, fwd_feas, _⟩ := Φ
  subst hΦ
  exact d_infeasible _ (fwd_feas p3 tour3 tour3_feasible)

-- ============================================================================
-- § Unrestricted-Parameter Reformulation
-- ============================================================================

private def adGammaA (p : P12.a.Params) (hn : p.n = 3) : ℝ :=
  p.c ⟨0, by omega⟩ ⟨1, by omega⟩ +
    p.c ⟨1, by omega⟩ ⟨2, by omega⟩ +
    p.c ⟨2, by omega⟩ ⟨0, by omega⟩

private def adGammaB (p : P12.a.Params) (hn : p.n = 3) : ℝ :=
  p.c ⟨0, by omega⟩ ⟨2, by omega⟩ +
    p.c ⟨2, by omega⟩ ⟨1, by omega⟩ +
    p.c ⟨1, by omega⟩ ⟨0, by omega⟩

private def adTargetParams4 (p : P12.a.Params) (hn : p.n = 3) : P12.d.Params :=
  { n := 4
    c := fun i j =>
      if i.val = 0 then
        if j.val = 2 then adGammaB p hn else adGammaA p hn
      else 0
    hn := by omega }

private def adParamMap (p : P12.a.Params) : P12.d.Params :=
  if hn : p.n = 3 then
    adTargetParams4 p hn
  else
    { n := p.n, c := p.c, hn := p.hn }

private def adSourceTourA (p : P12.a.Params) : P12.a.Vars p :=
  { x := fun i j =>
      if (i.val = 0 ∧ j.val = 1) ∨
          (i.val = 1 ∧ j.val = 2) ∨
          (i.val = 2 ∧ j.val = 0) then 1 else 0
    u := fun i =>
      if i.val = 0 then 1 else if i.val = 1 then 2 else 3 }

private def adSourceTourB (p : P12.a.Params) : P12.a.Vars p :=
  { x := fun i j =>
      if (i.val = 0 ∧ j.val = 2) ∨
          (i.val = 2 ∧ j.val = 1) ∨
          (i.val = 1 ∧ j.val = 0) then 1 else 0
    u := fun i =>
      if i.val = 0 then 1 else if i.val = 1 then 3 else 2 }

private def adTargetTourA (p : P12.a.Params) (hn : p.n = 3) :
    P12.d.Vars (adTargetParams4 p hn) :=
  { x := fun i j =>
      if (i.val = 0 ∧ j.val = 1) ∨
          (i.val = 1 ∧ j.val = 2) ∨
          (i.val = 2 ∧ j.val = 3) ∨
          (i.val = 3 ∧ j.val = 0) then 1 else 0
    u := fun i => i.val + 1 }

private def adTargetTourB (p : P12.a.Params) (hn : p.n = 3) :
    P12.d.Vars (adTargetParams4 p hn) :=
  { x := fun i j =>
      if (i.val = 0 ∧ j.val = 2) ∨
          (i.val = 2 ∧ j.val = 1) ∨
          (i.val = 1 ∧ j.val = 3) ∨
          (i.val = 3 ∧ j.val = 0) then 1 else 0
    u := fun i =>
      if i.val = 0 then 1
      else if i.val = 2 then 2
      else if i.val = 1 then 3
      else 4 }

private def adFwd (p : P12.a.Params) (v : P12.a.Vars p) :
    P12.d.Vars (adParamMap p) :=
  if hn : p.n = 3 then
    if v.x ⟨0, by omega⟩ ⟨1, by omega⟩ = 1 then
      cast (by simp [adParamMap, hn]) (adTargetTourA p hn)
    else
      cast (by simp [adParamMap, hn]) (adTargetTourB p hn)
  else
    cast (by simp [adParamMap, hn])
      ({ x := v.x, u := v.u } :
        P12.d.Vars { n := p.n, c := p.c, hn := p.hn })

private def adBwd (p : P12.a.Params) (v : P12.d.Vars (adParamMap p)) :
    P12.a.Vars p :=
  if hn : p.n = 3 then
    let w : P12.d.Vars (adTargetParams4 p hn) :=
      cast (by simp [adParamMap, hn]) v
    if w.x ⟨0, by simp [adTargetParams4]⟩ ⟨2, by simp [adTargetParams4]⟩ = 1 then
      adSourceTourB p
    else
      adSourceTourA p
  else
    let w : P12.d.Vars { n := p.n, c := p.c, hn := p.hn } :=
      cast (by simp [adParamMap, hn]) v
    { x := w.x, u := w.u }

private lemma adDFeasibleCast {q q' : P12.d.Params} (hq : q = q')
    (v : P12.d.Vars q) (h : P12.d.Feasible q v) :
    P12.d.Feasible q' (cast (congrArg P12.d.Vars hq) v) := by
  subst q'
  simpa

private lemma adDObjCast {q q' : P12.d.Params} (hq : q = q')
    (v : P12.d.Vars q) :
    P12.d.obj q' (cast (congrArg P12.d.Vars hq) v) = P12.d.obj q v := by
  subst q'
  rfl

private lemma adSourceTourAFeasible (p : P12.a.Params) (hn : p.n = 3) :
    P12.a.Feasible p (adSourceTourA p) := by
  rcases p with ⟨n, c, hp⟩
  simp only at hn
  subst n
  refine
    { hout := ?_, hin := ?_, hmtz := ?_, hu_depot := ?_, hx_bin := ?_,
      hu_lo := ?_, hu_hi := ?_, hx_no_self := ?_ }
  · intro i
    fin_cases i <;> rw [Fin.sum_univ_three] <;>
      norm_num [adSourceTourA]
    all_goals
      intro heq
      have hval := congrArg Fin.val heq
      norm_num at hval
  · intro j
    fin_cases j <;> rw [Fin.sum_univ_three] <;>
      norm_num [adSourceTourA]
    all_goals
      intro heq
      have hval := congrArg Fin.val heq
      norm_num at hval
  · intro i j hi hj hij
    fin_cases i <;> fin_cases j <;>
      norm_num [adSourceTourA] at *
  · norm_num [adSourceTourA]
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [adSourceTourA]
  · intro i hi
    fin_cases i <;> norm_num [adSourceTourA] at *
  · intro i
    fin_cases i <;> norm_num [adSourceTourA]
  · intro i
    fin_cases i <;> norm_num [adSourceTourA]

private lemma adSourceTourBFeasible (p : P12.a.Params) (hn : p.n = 3) :
    P12.a.Feasible p (adSourceTourB p) := by
  rcases p with ⟨n, c, hp⟩
  simp only at hn
  subst n
  refine
    { hout := ?_, hin := ?_, hmtz := ?_, hu_depot := ?_, hx_bin := ?_,
      hu_lo := ?_, hu_hi := ?_, hx_no_self := ?_ }
  · intro i
    fin_cases i <;> rw [Fin.sum_univ_three] <;>
      norm_num [adSourceTourB]
    all_goals
      intro heq
      have hval := congrArg Fin.val heq
      norm_num at hval
  · intro j
    fin_cases j <;> rw [Fin.sum_univ_three] <;>
      norm_num [adSourceTourB]
    all_goals
      intro heq
      have hval := congrArg Fin.val heq
      norm_num at hval
  · intro i j hi hj hij
    fin_cases i <;> fin_cases j <;>
      norm_num [adSourceTourB] at *
  · norm_num [adSourceTourB]
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [adSourceTourB]
  · intro i hi
    fin_cases i <;> norm_num [adSourceTourB] at *
  · intro i
    fin_cases i <;> norm_num [adSourceTourB]
  · intro i
    fin_cases i <;> norm_num [adSourceTourB]

private lemma adTargetTourAFeasible (p : P12.a.Params) (hn : p.n = 3) :
    P12.d.Feasible (adTargetParams4 p hn) (adTargetTourA p hn) := by
  refine
    { hout := ?_, hin := ?_, hmtz := ?_, hu_depot := ?_, hx_bin := ?_,
      hu_lo := ?_, hu_hi := ?_, hec3 := ?_, hx_no_self := ?_ }
  · intro i
    simp only [adTargetTourA, adTargetParams4]
    fin_cases i <;> rw [Fin.sum_univ_four] <;>
      norm_num [adTargetTourA, adTargetParams4]
  · intro j
    simp only [adTargetTourA, adTargetParams4]
    fin_cases j <;> rw [Fin.sum_univ_four] <;>
      norm_num [adTargetTourA, adTargetParams4]
  · intro i j hi hj hij
    fin_cases i <;> fin_cases j <;>
      norm_num [adTargetTourA, adTargetParams4] at *
  · norm_num [adTargetTourA, adTargetParams4]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [adTargetTourA, adTargetParams4]
  · intro i hi
    fin_cases i <;> norm_num [adTargetTourA, adTargetParams4] at *
  · intro i
    fin_cases i <;> norm_num [adTargetTourA, adTargetParams4]
  · intro i j hi hj hij
    fin_cases i <;> fin_cases j <;>
      norm_num [adTargetTourA, adTargetParams4] at *
  · intro i
    fin_cases i <;> norm_num [adTargetTourA, adTargetParams4]

private lemma adTargetTourBFeasible (p : P12.a.Params) (hn : p.n = 3) :
    P12.d.Feasible (adTargetParams4 p hn) (adTargetTourB p hn) := by
  refine
    { hout := ?_, hin := ?_, hmtz := ?_, hu_depot := ?_, hx_bin := ?_,
      hu_lo := ?_, hu_hi := ?_, hec3 := ?_, hx_no_self := ?_ }
  · intro i
    simp only [adTargetTourB, adTargetParams4]
    fin_cases i <;> rw [Fin.sum_univ_four] <;>
      norm_num [adTargetTourB, adTargetParams4]
  · intro j
    simp only [adTargetTourB, adTargetParams4]
    fin_cases j <;> rw [Fin.sum_univ_four] <;>
      norm_num [adTargetTourB, adTargetParams4]
  · intro i j hi hj hij
    fin_cases i <;> fin_cases j <;>
      norm_num [adTargetTourB, adTargetParams4] at *
  · norm_num [adTargetTourB, adTargetParams4]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [adTargetTourB, adTargetParams4]
  · intro i hi
    fin_cases i <;> norm_num [adTargetTourB, adTargetParams4] at *
  · intro i
    fin_cases i <;> norm_num [adTargetTourB, adTargetParams4]
  · intro i j hi hj hij
    fin_cases i <;> fin_cases j <;>
      norm_num [adTargetTourB, adTargetParams4] at *
  · intro i
    fin_cases i <;> norm_num [adTargetTourB, adTargetParams4]

private lemma adSourceEqTourA (p : P12.a.Params) (v : P12.a.Vars p)
    (h : P12.a.Feasible p v) (hn : p.n = 3)
    (hx : v.x ⟨0, by omega⟩ ⟨1, by omega⟩ = 1) :
    adSourceTourA p = v := by
  rcases p with ⟨n, c, hp⟩
  simp only at hn
  subst n
  cases v with
  | mk x u =>
    have ho0 := h.hout 0
    have ho1 := h.hout 1
    have ho2 := h.hout 2
    have hi0 := h.hin 0
    have hi1 := h.hin 1
    have hi2 := h.hin 2
    rw [Fin.sum_univ_three] at ho0 ho1 ho2 hi0 hi1 hi2
    have hs0 := h.hx_no_self 0
    have hs1 := h.hx_no_self 1
    have hs2 := h.hx_no_self 2
    simp only at ho0 ho1 ho2 hi0 hi1 hi2 hs0 hs1 hs2 hx
    have hx01 : x 0 1 = 1 := by simpa using hx
    have h1ne0 : (1 : Fin 3).val ≠ 0 := by norm_num
    have h2ne0 : (2 : Fin 3).val ≠ 0 := by norm_num
    have h1ne2 : (1 : Fin 3) ≠ 2 := by decide
    have hm := h.hmtz (1 : Fin 3) (2 : Fin 3)
      h1ne0 h2ne0 h1ne2
    have hx12 : x 1 2 = 1 := by omega
    have ex00 : x 0 0 = 0 := hs0
    have ex01 : x 0 1 = 1 := hx01
    have ex02 : x 0 2 = 0 := by omega
    have ex10 : x 1 0 = 0 := by omega
    have ex11 : x 1 1 = 0 := hs1
    have ex12 : x 1 2 = 1 := hx12
    have ex20 : x 2 0 = 1 := by omega
    have ex21 : x 2 1 = 0 := by omega
    have ex22 : x 2 2 = 0 := hs2
    have hx12r : (x 1 2 : ℝ) = 1 := by exact_mod_cast hx12
    rw [hx12r] at hm
    norm_num at hm
    have hu0 : u 0 = 1 := by simpa using h.hu_depot
    have hlo1 := h.hu_lo 1 (by norm_num)
    have hhi2 := h.hu_hi 2
    norm_num at hhi2
    have hu1 : u 1 = 2 := by linarith
    have hu2 : u 2 = 3 := by linarith
    rw [P12.a.Vars.mk.injEq]
    constructor
    · funext i j
      fin_cases i <;> fin_cases j <;>
        simp [adSourceTourA, ex00, ex01, ex02, ex10, ex11, ex12, ex20, ex21,
          ex22]
    · funext i
      fin_cases i
      · simpa [adSourceTourA] using hu0.symm
      · simpa [adSourceTourA] using hu1.symm
      · simpa [adSourceTourA] using hu2.symm

private lemma adSourceEqTourB (p : P12.a.Params) (v : P12.a.Vars p)
    (h : P12.a.Feasible p v) (hn : p.n = 3)
    (hx : v.x ⟨0, by omega⟩ ⟨1, by omega⟩ ≠ 1) :
    adSourceTourB p = v := by
  rcases p with ⟨n, c, hp⟩
  simp only at hn
  subst n
  cases v with
  | mk x u =>
    have ho0 := h.hout 0
    have ho1 := h.hout 1
    have ho2 := h.hout 2
    have hi0 := h.hin 0
    have hi1 := h.hin 1
    have hi2 := h.hin 2
    rw [Fin.sum_univ_three] at ho0 ho1 ho2 hi0 hi1 hi2
    have hs0 := h.hx_no_self 0
    have hs1 := h.hx_no_self 1
    have hs2 := h.hx_no_self 2
    simp only at ho0 ho1 ho2 hi0 hi1 hi2 hs0 hs1 hs2 hx
    have hx01ne : x 0 1 ≠ 1 := by simpa using hx
    have hx01 : x 0 1 = 0 := (h.hx_bin 0 1).resolve_right hx01ne
    have h2ne0 : (2 : Fin 3).val ≠ 0 := by norm_num
    have h1ne0 : (1 : Fin 3).val ≠ 0 := by norm_num
    have h2ne1 : (2 : Fin 3) ≠ 1 := by decide
    have hm := h.hmtz (2 : Fin 3) (1 : Fin 3)
      h2ne0 h1ne0 h2ne1
    have hx21 : x 2 1 = 1 := by omega
    have ex00 : x 0 0 = 0 := hs0
    have ex01 : x 0 1 = 0 := hx01
    have ex02 : x 0 2 = 1 := by omega
    have ex10 : x 1 0 = 1 := by omega
    have ex11 : x 1 1 = 0 := hs1
    have ex12 : x 1 2 = 0 := by omega
    have ex20 : x 2 0 = 0 := by omega
    have ex21 : x 2 1 = 1 := hx21
    have ex22 : x 2 2 = 0 := hs2
    have hx21r : (x 2 1 : ℝ) = 1 := by exact_mod_cast hx21
    rw [hx21r] at hm
    norm_num at hm
    have hu0 : u 0 = 1 := by simpa using h.hu_depot
    have hlo2 := h.hu_lo 2 (by norm_num)
    have hhi1 := h.hu_hi 1
    norm_num at hhi1
    have hu2 : u 2 = 2 := by linarith
    have hu1 : u 1 = 3 := by linarith
    rw [P12.a.Vars.mk.injEq]
    constructor
    · funext i j
      fin_cases i <;> fin_cases j <;>
        simp [adSourceTourB, ex00, ex01, ex02, ex10, ex11, ex12, ex20, ex21,
          ex22]
    · funext i
      fin_cases i
      · simpa [adSourceTourB] using hu0.symm
      · simpa [adSourceTourB] using hu1.symm
      · simpa [adSourceTourB] using hu2.symm

private lemma xnn {p : P12.a.Params} {v : P12.a.Vars p} (h : P12.a.Feasible p v)
    (a b : Fin p.n) : 0 ≤ v.x a b := by
  rcases h.hx_bin a b with h0 | h1 <;> omega

/-- Each node has a unique outgoing arc in Fin p.n. -/
private lemma exists_unique_out {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) (i : Fin p.n) :
    ∃! k : Fin p.n, v.x i k = 1 := by
  haveI : NeZero p.n := ⟨by have := p.hn; omega⟩
  have hsum := h.hout i
  have hex : ∃ k : Fin p.n, v.x i k = 1 := by
    by_contra hc
    push_neg at hc
    have h0 : ∀ k : Fin p.n, v.x i k = 0 := fun k =>
      (h.hx_bin i k).resolve_right (hc k)
    simp [h0] at hsum
  obtain ⟨k, hk⟩ := hex
  refine ⟨k, hk, fun k' hk' => ?_⟩
  by_contra hne
  have hge : ∑ j : Fin p.n, v.x i j ≥ v.x i k + v.x i k' :=
    calc ∑ j : Fin p.n, v.x i j
        ≥ ∑ j ∈ ({k, k'} : Finset (Fin p.n)), v.x i j :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _)
            (fun j _ _ => xnn h i j)
      _ = v.x i k + v.x i k' := sum_pair (Ne.symm hne)
  linarith

/-- Each node has a unique incoming arc in Fin p.n. -/
private lemma exists_unique_in {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) (j : Fin p.n) :
    ∃! k : Fin p.n, v.x k j = 1 := by
  haveI : NeZero p.n := ⟨by have := p.hn; omega⟩
  have hsum := h.hin j
  have hex : ∃ k : Fin p.n, v.x k j = 1 := by
    by_contra hc
    push_neg at hc
    have h0 : ∀ k : Fin p.n, v.x k j = 0 := fun k =>
      (h.hx_bin k j).resolve_right (hc k)
    simp [h0] at hsum
  obtain ⟨k, hk⟩ := hex
  refine ⟨k, hk, fun k' hk' => ?_⟩
  by_contra hne
  have hge : ∑ i : Fin p.n, v.x i j ≥ v.x k j + v.x k' j :=
    calc ∑ i : Fin p.n, v.x i j
        ≥ ∑ i ∈ ({k, k'} : Finset (Fin p.n)), v.x i j :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _)
            (fun i _ _ => xnn h i j)
      _ = v.x k j + v.x k' j := sum_pair (Ne.symm hne)
  linarith

/-- The successor of i (unique k with x i k = 1), as Fin p.n. -/
private noncomputable def succF {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) (i : Fin p.n) : Fin p.n :=
  (exists_unique_out h i).choose

private lemma succF_spec {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) (i : Fin p.n) : v.x i (succF h i) = 1 :=
  (exists_unique_out h i).choose_spec.1

private lemma succF_unique {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) (i k : Fin p.n) (hk : v.x i k = 1) :
    k = succF h i := by
  obtain ⟨w, hw, hun⟩ := exists_unique_out h i
  have h1 : k = w := hun k hk
  have h2 : succF h i = w := hun (succF h i) (succF_spec h i)
  rw [h1, h2]

private lemma succF_injective {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) : Function.Injective (succF h) := by
  intro a b hab
  have ha := succF_spec h a
  have hb := succF_spec h b
  rw [hab] at ha
  by_contra hne
  have hin := h.hin (succF h b)
  have hge : ∑ j : Fin p.n, v.x j (succF h b) ≥
      v.x a (succF h b) + v.x b (succF h b) :=
    calc ∑ j : Fin p.n, v.x j (succF h b)
        ≥ ∑ j ∈ ({a, b} : Finset (Fin p.n)), v.x j (succF h b) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _)
            (fun j _ _ => xnn h j (succF h b))
      _ = v.x a (succF h b) + v.x b (succF h b) := sum_pair hne
  linarith

private lemma succF_ne_self {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) (i : Fin p.n) : succF h i ≠ i := by
  intro heq
  have hs := succF_spec h i
  rw [heq] at hs
  have : v.x i i = 0 := h.hx_no_self i
  omega

/-- MTZ gives strict position increase along non-depot arcs. -/
private lemma pos_increase {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) {a : Fin p.n} (ha : a.val ≠ 0)
    (hsa : (succF h a).val ≠ 0) :
    v.u a + 1 ≤ v.u (succF h a) := by
  have hx := succF_spec h a
  have hne := succF_ne_self h a
  have hmtz := h.hmtz a (succF h a) ha hsa (Ne.symm hne)
  have hcast : (v.x a (succF h a) : ℝ) = 1 := by exact_mod_cast hx
  nlinarith [hmtz, hcast]

private lemma pos_iterate_increase {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) {m : Fin p.n} (_hm : m.val ≠ 0) {k : ℕ}
    (hall : ∀ i : ℕ, i ≤ k → ((succF h)^[i] m).val ≠ 0) :
    v.u m + k ≤ v.u ((succF h)^[k] m) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hall_k : ∀ i, i ≤ k → ((succF h)^[i] m).val ≠ 0 :=
      fun i hi => hall i (by omega)
    have hk_ne : ((succF h)^[k] m).val ≠ 0 := hall k (Nat.le_succ k)
    have hsk_ne : ((succF h)^[k + 1] m).val ≠ 0 := hall (k + 1) le_rfl
    have ih' := ih hall_k
    rw [Function.iterate_succ', Function.comp_apply]
    rw [Function.iterate_succ', Function.comp_apply] at hsk_ne
    have step := pos_increase h hk_ne hsk_ne
    push_cast; linarith

private lemma reaches_depot {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) (m : Fin p.n) :
    ∃ k : ℕ, ((succF h)^[k] m).val = 0 := by
  haveI : NeZero p.n := ⟨by have := p.hn; omega⟩
  by_contra hc
  push_neg at hc
  have hall : ∀ i : ℕ, ((succF h)^[i] m).val ≠ 0 := hc
  have hm : m.val ≠ 0 := hall 0
  have hgrow : ∀ k : ℕ, v.u m + k ≤ v.u ((succF h)^[k] m) :=
    fun k => pos_iterate_increase h hm (fun i _ => hall i)
  have hbound := h.hu_hi ((succF h)^[p.n] m)
  have hpn := hgrow p.n
  have hlo := h.hu_lo m hm
  linarith

private lemma no_nondepot_period {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) {m : Fin p.n} (hm : m.val ≠ 0) {q : ℕ} (hq : 0 < q)
    (hperiod : (succF h)^[q] m = m)
    (hall : ∀ i, i ≤ q → ((succF h)^[i] m).val ≠ 0) : False := by
  have hinc := pos_iterate_increase h hm hall
  rw [hperiod] at hinc
  have : (q : ℝ) > 0 := Nat.cast_pos.mpr hq
  linarith

private lemma succF_bijective {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) : Function.Bijective (succF h) :=
  Finite.injective_iff_bijective.mp (succF_injective h)

private lemma min_reaches_depot {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) (m : Fin p.n) :
    ∃ k : ℕ, ((succF h)^[k] m).val = 0 ∧
      ∀ i, i < k → ((succF h)^[i] m).val ≠ 0 := by
  have hex := reaches_depot h m
  refine ⟨Nat.find hex, Nat.find_spec hex, fun i hi heq => ?_⟩
  exact Nat.find_min hex hi heq

private lemma chain_length_aux {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) (j : Fin p.n) (_hj : j.val ≠ 0)
    (hxj : haveI : NeZero p.n := ⟨by have := p.hn; omega⟩; v.x 0 j = 1) :
    ∃ k : ℕ, k = p.n - 1 ∧ ((succF h)^[k] j).val = 0 ∧
      ∀ i, i < k → ((succF h)^[i] j).val ≠ 0 := by
  haveI : NeZero p.n := ⟨by have := p.hn; omega⟩
  have hn_pos : 0 < p.n := Nat.pos_of_ne_zero (NeZero.ne p.n)
  obtain ⟨k, hk_zero, hk_nondepot⟩ := min_reaches_depot h j
  refine ⟨k, ?_, hk_zero, hk_nondepot⟩
  have hk_le : k ≤ p.n - 1 := by
    by_contra hlt; push_neg at hlt
    have hninj : ¬ Function.Injective (fun i : Fin p.n => (succF h)^[i.val] j) := by
      intro hinj
      have h0_not : ∀ i : Fin p.n, ((succF h)^[i.val] j).val ≠ 0 :=
        fun i => hk_nondepot i.val (by omega)
      have hsurj := Finite.injective_iff_surjective.mp hinj
      obtain ⟨i, hi⟩ := hsurj ⟨0, hn_pos⟩
      simp only at hi
      have hvz : ((succF h)^[i.val] j).val = 0 := by rw [hi]
      exact h0_not i hvz
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab_eq, hab_ne⟩ :=
      (Function.not_injective_iff.mp hninj : ∃ a b : Fin p.n, _)
    simp only at hab_eq
    have hab_ne' : a ≠ b := fun heq => hab_ne (Fin.ext heq)
    rcases Nat.lt_or_gt_of_ne hab_ne' with hab | hab <;> {
      have h1_ne := hk_nondepot (min a b) (by omega)
      have h1_period : (succF h)^[max a b - min a b] ((succF h)^[min a b] j) =
          (succF h)^[min a b] j := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel (min_le_max (a := a) (b := b))]
        simp only [Nat.max_def, Nat.min_def] at *
        split_ifs <;> [exact hab_eq.symm; exact hab_eq]
      have h1_hall : ∀ i, i ≤ max a b - min a b →
          ((succF h)^[i] ((succF h)^[min a b] j)).val ≠ 0 := by
        intro i hi; rw [← Function.iterate_add_apply]; exact hk_nondepot _ (by omega)
      exact no_nondepot_period h h1_ne (by omega) h1_period h1_hall }
  have hk_ge : p.n - 1 ≤ k := by
    let σ : Equiv.Perm (Fin p.n) := Equiv.ofBijective (succF h) (succF_bijective h)
    have hsucc0 : succF h ⟨0, hn_pos⟩ = j :=
      (succF_unique h ⟨0, hn_pos⟩ j hxj).symm
    have hperiod : (σ ^ (k + 1)) (⟨0, hn_pos⟩ : Fin p.n) = ⟨0, hn_pos⟩ := by
      show (succF h)^[k + 1] ⟨0, hn_pos⟩ = ⟨0, hn_pos⟩
      rw [Function.iterate_succ_apply, hsucc0]
      exact Fin.ext hk_zero
    suffices horbit : ∀ m : Fin p.n,
        ∃ q, q ≤ k ∧ (σ ^ q) (⟨0, hn_pos⟩ : Fin p.n) = m by
      have hsurj : Function.Surjective
          (fun i : Fin (k + 1) => (σ ^ i.val) (⟨0, hn_pos⟩ : Fin p.n)) := by
        intro m; obtain ⟨q, hq, hqe⟩ := horbit m; exact ⟨⟨q, by omega⟩, hqe⟩
      have := Fintype.card_le_of_surjective _ hsurj
      simp [Fintype.card_fin] at this; omega
    suffices hinv : ∀ q (m : Fin p.n), (σ ^ q) m = ⟨0, hn_pos⟩ →
        ∃ r, r ≤ k ∧ (σ ^ r) (⟨0, hn_pos⟩ : Fin p.n) = m by
      intro m
      obtain ⟨q, hq⟩ := reaches_depot h m
      refine hinv q m ?_
      show (succF h)^[q] m = ⟨0, hn_pos⟩
      exact Fin.ext hq
    intro q
    induction q with
    | zero =>
      intro m hm; simp at hm; exact ⟨0, Nat.zero_le k, by simp [hm]⟩
    | succ q ih =>
      intro m hm
      rw [pow_succ, Equiv.Perm.mul_apply] at hm
      obtain ⟨r, hr, hre⟩ := ih (σ m) hm
      by_cases hr0 : r = 0
      · subst hr0; simp at hre
        refine ⟨k, le_refl k, ?_⟩
        have hσk : σ ((σ ^ k) (⟨0, hn_pos⟩ : Fin p.n)) = ⟨0, hn_pos⟩ := by
          rw [← Equiv.Perm.mul_apply, ← pow_succ']; exact hperiod
        exact σ.injective (hσk.trans hre)
      · refine ⟨r - 1, by omega, ?_⟩
        have hpred : (σ ^ r) (⟨0, hn_pos⟩ : Fin p.n) =
            σ ((σ ^ (r - 1)) (⟨0, hn_pos⟩ : Fin p.n)) := by
          conv_lhs => rw [show r = (r - 1) + 1 from by omega, pow_succ',
            Equiv.Perm.mul_apply]
        exact σ.injective (hpred.symm.trans hre)
  omega

/-- When j → i (x_{ji} = 1) with i, j ∈ Fin p.n non-depot, u i = u j + 1. -/
private lemma arc_consec_nondepot {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) {i j : Fin p.n} (hi : i.val ≠ 0) (hj : j.val ≠ 0)
    (hxji : v.x j i = 1) : v.u i = v.u j + 1 := by
  haveI : NeZero p.n := ⟨by have := p.hn; omega⟩
  have hn_pos : 0 < p.n := Nat.pos_of_ne_zero (NeZero.ne p.n)
  have hn2 : 2 ≤ p.n := by
    by_contra hlt; push_neg at hlt
    have hjlt := j.isLt
    exact hj (by omega)
  have hsucc_j : succF h j = i := (succF_unique h j i hxji).symm
  have hlb : v.u j + 1 ≤ v.u i := by
    have := pos_increase h hj (hsucc_j ▸ hi)
    rw [hsucc_j] at this; exact this
  set j0 : Fin p.n := succF h ⟨0, hn_pos⟩ with hj0_def
  have hj0_ne : j0.val ≠ 0 := by
    intro h0
    have : succF h ⟨0, hn_pos⟩ = ⟨0, hn_pos⟩ := Fin.ext h0
    exact succF_ne_self h ⟨0, hn_pos⟩ this
  have hx0j0 : v.x 0 j0 = 1 := by
    have := succF_spec h (⟨0, hn_pos⟩ : Fin p.n)
    simpa using this
  obtain ⟨k, hk_eq, hk_zero, hk_nd⟩ := chain_length_aux h j0 hj0_ne hx0j0
  have hj_in_orbit : ∃ a : ℕ, a ≤ p.n - 2 ∧ (succF h)^[a] j0 = j := by
    let σ : Equiv.Perm (Fin p.n) := Equiv.ofBijective (succF h) (succF_bijective h)
    have hperiod : (σ ^ (k + 1)) (⟨0, hn_pos⟩ : Fin p.n) = ⟨0, hn_pos⟩ := by
      show (succF h)^[k + 1] ⟨0, hn_pos⟩ = ⟨0, hn_pos⟩
      rw [Function.iterate_succ_apply]
      change (succF h)^[k] j0 = ⟨0, hn_pos⟩
      exact Fin.ext hk_zero
    have horbit : ∀ m : Fin p.n,
        ∃ r, r ≤ k ∧ (σ ^ r) (⟨0, hn_pos⟩ : Fin p.n) = m := by
      suffices hinv : ∀ q (m : Fin p.n), (σ ^ q) m = ⟨0, hn_pos⟩ →
          ∃ r, r ≤ k ∧ (σ ^ r) (⟨0, hn_pos⟩ : Fin p.n) = m by
        intro m
        obtain ⟨q, hq⟩ := reaches_depot h m
        refine hinv q m ?_
        show (succF h)^[q] m = ⟨0, hn_pos⟩
        exact Fin.ext hq
      intro q
      induction q with
      | zero =>
        intro m hm; simp at hm; exact ⟨0, Nat.zero_le k, by simp [hm]⟩
      | succ q ih =>
        intro m hm
        rw [pow_succ, Equiv.Perm.mul_apply] at hm
        obtain ⟨r, hr, hre⟩ := ih (σ m) hm
        by_cases hr0 : r = 0
        · subst hr0; simp at hre
          refine ⟨k, le_refl k, ?_⟩
          have hσk : σ ((σ ^ k) (⟨0, hn_pos⟩ : Fin p.n)) = ⟨0, hn_pos⟩ := by
            rw [← Equiv.Perm.mul_apply, ← pow_succ']; exact hperiod
          exact σ.injective (hσk.trans hre)
        · refine ⟨r - 1, by omega, ?_⟩
          have hpred : (σ ^ r) (⟨0, hn_pos⟩ : Fin p.n) =
              σ ((σ ^ (r - 1)) (⟨0, hn_pos⟩ : Fin p.n)) := by
            conv_lhs => rw [show r = (r - 1) + 1 from by omega, pow_succ',
              Equiv.Perm.mul_apply]
          exact σ.injective (hpred.symm.trans hre)
    obtain ⟨r, hr, hre⟩ := horbit j
    have hr_pos : 1 ≤ r := by
      by_contra hc; push_neg at hc
      interval_cases r; simp at hre
      exact hj (by rw [← hre]; rfl)
    refine ⟨r - 1, by omega, ?_⟩
    show (succF h)^[r - 1] j0 = j
    have heq : (σ ^ r) (⟨0, hn_pos⟩ : Fin p.n) = (succF h)^[r] ⟨0, hn_pos⟩ := rfl
    rw [heq] at hre
    have hshift : (succF h)^[r] (⟨0, hn_pos⟩ : Fin p.n) = (succF h)^[r - 1] j0 := by
      conv_lhs => rw [show r = (r - 1) + 1 from by omega]
      rw [Function.iterate_succ_apply]
    rw [hshift] at hre; exact hre
  obtain ⟨a, ha_le, ha_eq⟩ := hj_in_orbit
  have hi_eq : (succF h)^[a + 1] j0 = i := by
    rw [Function.iterate_succ_apply', ha_eq]; exact hsucc_j
  have hj0_all_nd : ∀ s, s ≤ p.n - 2 → ((succF h)^[s] j0).val ≠ 0 :=
    fun s hs => hk_nd s (by omega)
  by_cases hcase : a + 1 ≤ p.n - 2
  · have ha1_nd : ((succF h)^[a + 1] j0).val ≠ 0 := hk_nd (a + 1) (by omega)
    have hall_j0 : ∀ s, s ≤ p.n - 2 → ((succF h)^[s] j0).val ≠ 0 := hj0_all_nd
    have hinc_j0_last := pos_iterate_increase h hj0_ne hall_j0 (k := p.n - 2)
    have hcast_nm2 : ((p.n - 2 : ℕ) : ℝ) = (p.n : ℝ) - 2 := by
      rw [Nat.cast_sub hn2]; norm_num
    have hj0_pos_ub : v.u j0 ≤ 2 := by
      have hu_last_ub := h.hu_hi ((succF h)^[p.n - 2] j0)
      rw [hcast_nm2] at hinc_j0_last
      linarith
    have hj0_pos_lb : (2 : ℝ) ≤ v.u j0 := h.hu_lo j0 hj0_ne
    have hj0_pos : v.u j0 = 2 := le_antisymm hj0_pos_ub hj0_pos_lb
    have hu_last : v.u ((succF h)^[p.n - 2] j0) = (p.n : ℝ) := by
      have hu_last_ub := h.hu_hi ((succF h)^[p.n - 2] j0)
      rw [hcast_nm2, hj0_pos] at hinc_j0_last
      linarith
    have hu_a1_eq : v.u ((succF h)^[a + 1] j0) = 2 + ((a + 1 : ℕ) : ℝ) := by
      have hall_a1 : ∀ s, s ≤ a + 1 → ((succF h)^[s] j0).val ≠ 0 :=
        fun s hs => hj0_all_nd s (by omega)
      have hinc_a1 := pos_iterate_increase h hj0_ne hall_a1
      have hstep_tail : ∀ s, s ≤ p.n - 2 - (a + 1) →
          ((succF h)^[s] ((succF h)^[a + 1] j0)).val ≠ 0 := by
        intro s hs; rw [← Function.iterate_add_apply]; exact hj0_all_nd _ (by omega)
      have hinc_tail := pos_iterate_increase h ha1_nd hstep_tail
      have heq_tail : (succF h)^[p.n - 2 - (a + 1)] ((succF h)^[a + 1] j0) =
          (succF h)^[p.n - 2] j0 := by
        rw [← Function.iterate_add_apply]; congr 1; omega
      rw [heq_tail, hu_last] at hinc_tail
      rw [hj0_pos] at hinc_a1
      have hcast_tail : ((p.n - 2 - (a + 1) : ℕ) : ℝ) = (p.n : ℝ) - 2 - ((a + 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hcase, hcast_nm2]
      rw [hcast_tail] at hinc_tail
      linarith
    have hu_a_eq : v.u ((succF h)^[a] j0) = 2 + (a : ℝ) := by
      by_cases ha0 : a = 0
      · subst ha0; simp; rw [hj0_pos]
      · have ha_pos : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
        have ha_le' : a ≤ p.n - 2 := by omega
        have hall_a : ∀ s, s ≤ a → ((succF h)^[s] j0).val ≠ 0 :=
          fun s hs => hj0_all_nd s (by omega)
        have hinc_a := pos_iterate_increase h hj0_ne hall_a
        have ha_nd : ((succF h)^[a] j0).val ≠ 0 := hj0_all_nd a (by omega)
        have hstep_a : ∀ s, s ≤ p.n - 2 - a →
            ((succF h)^[s] ((succF h)^[a] j0)).val ≠ 0 := by
          intro s hs; rw [← Function.iterate_add_apply]; exact hj0_all_nd _ (by omega)
        have hinc_a_tail := pos_iterate_increase h ha_nd hstep_a
        have heq_a_tail : (succF h)^[p.n - 2 - a] ((succF h)^[a] j0) =
            (succF h)^[p.n - 2] j0 := by
          rw [← Function.iterate_add_apply]; congr 1; omega
        rw [heq_a_tail, hu_last] at hinc_a_tail
        rw [hj0_pos] at hinc_a
        have hcast_a : ((p.n - 2 - a : ℕ) : ℝ) = (p.n : ℝ) - 2 - (a : ℝ) := by
          rw [Nat.cast_sub ha_le', hcast_nm2]
        rw [hcast_a] at hinc_a_tail
        linarith
    rw [← ha_eq, ← hi_eq, hu_a_eq, hu_a1_eq]
    push_cast; ring
  · push_neg at hcase
    have ha1_eq : a + 1 = p.n - 1 := by omega
    have hi_is_zero : i.val = 0 := by
      rw [← hi_eq, ha1_eq]
      have : (succF h)^[p.n - 1] j0 = ⟨0, hn_pos⟩ := by
        rw [← hk_eq]; exact Fin.ext hk_zero
      rw [this]
    exact absurd hi_is_zero hi

/-- If `x_{i0} = 1` and `i ≠ 0`, then `u_i = n`. -/
private lemma u_eq_n_of_arc_to_depot {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) {i : Fin p.n} (hi : i.val ≠ 0)
    (hxi0 : haveI : NeZero p.n := ⟨by have := p.hn; omega⟩; v.x i 0 = 1) : v.u i = (p.n : ℝ) := by
  haveI : NeZero p.n := ⟨by have := p.hn; omega⟩
  have hn_pos : 0 < p.n := Nat.pos_of_ne_zero (NeZero.ne p.n)
  have hn2 : 2 ≤ p.n := by
    by_contra hlt; push_neg at hlt
    have hilt := i.isLt
    exact hi (by omega)
  -- succF h i = 0
  have hsucc_i : succF h i = ⟨0, hn_pos⟩ :=
    (succF_unique h i ⟨0, hn_pos⟩ (by simpa using hxi0)).symm
  -- Set up j0 = succF h 0
  set j0 : Fin p.n := succF h ⟨0, hn_pos⟩ with hj0_def
  have hj0_ne : j0.val ≠ 0 := by
    intro h0
    have : succF h ⟨0, hn_pos⟩ = ⟨0, hn_pos⟩ := Fin.ext h0
    exact succF_ne_self h ⟨0, hn_pos⟩ this
  have hx0j0 : v.x 0 j0 = 1 := by
    have := succF_spec h (⟨0, hn_pos⟩ : Fin p.n)
    simpa using this
  obtain ⟨k, hk_eq, hk_zero, hk_nd⟩ := chain_length_aux h j0 hj0_ne hx0j0
  -- u j0 = 2 and u (succF^[p.n-2] j0) = p.n
  have hj0_all_nd : ∀ s, s ≤ p.n - 2 → ((succF h)^[s] j0).val ≠ 0 :=
    fun s hs => hk_nd s (by omega)
  have hinc_j0_last := pos_iterate_increase h hj0_ne hj0_all_nd (k := p.n - 2)
  have hcast_nm2 : ((p.n - 2 : ℕ) : ℝ) = (p.n : ℝ) - 2 := by
    rw [Nat.cast_sub hn2]; norm_num
  have hj0_pos_ub : v.u j0 ≤ 2 := by
    have hu_last_ub := h.hu_hi ((succF h)^[p.n - 2] j0)
    rw [hcast_nm2] at hinc_j0_last
    linarith
  have hj0_pos_lb : (2 : ℝ) ≤ v.u j0 := h.hu_lo j0 hj0_ne
  have hj0_pos : v.u j0 = 2 := le_antisymm hj0_pos_ub hj0_pos_lb
  have hu_last : v.u ((succF h)^[p.n - 2] j0) = (p.n : ℝ) := by
    have hu_last_ub := h.hu_hi ((succF h)^[p.n - 2] j0)
    rw [hcast_nm2, hj0_pos] at hinc_j0_last
    linarith
  -- Now show i = (succF h)^[p.n - 2] j0.
  -- Chain: (succF h)^[p.n - 1] j0 = 0 = succF h i, so by injectivity
  -- (succF h)^[p.n - 2] j0 = i (when p.n - 2 = (p.n - 1) - 1).
  have hk_eq' : k = p.n - 1 := hk_eq
  have hchain_last : (succF h)^[p.n - 1] j0 = ⟨0, hn_pos⟩ := by
    rw [← hk_eq']; exact Fin.ext hk_zero
  -- (succF h)^[p.n - 1] j0 = succF h ((succF h)^[p.n - 2] j0)
  have hstep : (succF h)^[p.n - 1] j0 = succF h ((succF h)^[p.n - 2] j0) := by
    conv_lhs => rw [show p.n - 1 = (p.n - 2) + 1 from by omega]
    rw [Function.iterate_succ_apply']
  rw [hstep] at hchain_last
  -- succF h i = ⟨0, hn_pos⟩ = succF h ((succF h)^[p.n - 2] j0)
  have hinj : (succF h)^[p.n - 2] j0 = i :=
    succF_injective h (hchain_last.trans hsucc_i.symm)
  rw [← hinj]; exact hu_last

/-- If `x_{0i} = 1` and `i ≠ 0`, then `u_i = 2`. -/
private lemma u_eq_2_of_arc_from_depot {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) {i : Fin p.n} (hi : i.val ≠ 0)
    (hx0i : haveI : NeZero p.n := ⟨by have := p.hn; omega⟩; v.x 0 i = 1) : v.u i = 2 := by
  haveI : NeZero p.n := ⟨by have := p.hn; omega⟩
  have hn_pos : 0 < p.n := Nat.pos_of_ne_zero (NeZero.ne p.n)
  have hn2 : 2 ≤ p.n := by
    by_contra hlt; push_neg at hlt
    have hilt := i.isLt
    exact hi (by omega)
  set j0 : Fin p.n := succF h ⟨0, hn_pos⟩ with hj0_def
  -- i = j0 since both are the unique successor of depot.
  have hi_eq : i = j0 := succF_unique h ⟨0, hn_pos⟩ i (by simpa using hx0i)
  have hj0_ne : j0.val ≠ 0 := by rw [← hi_eq]; exact hi
  have hx0j0 : v.x 0 j0 = 1 := by rw [← hi_eq]; exact hx0i
  obtain ⟨k, hk_eq, hk_zero, hk_nd⟩ := chain_length_aux h j0 hj0_ne hx0j0
  have hj0_all_nd : ∀ s, s ≤ p.n - 2 → ((succF h)^[s] j0).val ≠ 0 :=
    fun s hs => hk_nd s (by omega)
  have hinc_j0_last := pos_iterate_increase h hj0_ne hj0_all_nd (k := p.n - 2)
  have hcast_nm2 : ((p.n - 2 : ℕ) : ℝ) = (p.n : ℝ) - 2 := by
    rw [Nat.cast_sub hn2]; norm_num
  have hj0_pos_ub : v.u j0 ≤ 2 := by
    have hu_last_ub := h.hu_hi ((succF h)^[p.n - 2] j0)
    rw [hcast_nm2] at hinc_j0_last
    linarith
  have hj0_pos_lb : (2 : ℝ) ≤ v.u j0 := h.hu_lo j0 hj0_ne
  have hj0_pos : v.u j0 = 2 := le_antisymm hj0_pos_ub hj0_pos_lb
  rw [hi_eq]; exact hj0_pos

private lemma adEC3OfLarge (p : P12.a.Params) (v : P12.a.Vars p)
    (h : P12.a.Feasible p v) (hn : 4 ≤ p.n) :
    ∀ (i j : Fin p.n), i.val ≠ 0 → j.val ≠ 0 → i ≠ j →
      haveI : NeZero p.n := ⟨by have := p.hn; omega⟩
      (v.x j 0 : ℝ) + (v.x j i : ℝ) + (v.u j - v.u i - 1) ≤
        ((p.n : ℝ) - 1) * (2 - (v.x 0 i : ℝ) - (v.x i j : ℝ)) := by
  intro i j hi hj hij
  haveI : NeZero p.n := ⟨by have := p.hn; omega⟩
  have h0i : (0 : Fin p.n) ≠ i := by
    intro hzero
    exact hi (by rw [← hzero]; rfl)
  have hpairZ : v.x j 0 + v.x j i ≤ 1 := by
    have hsum := h.hout j
    have hge : ∑ k : Fin p.n, v.x j k ≥ v.x j 0 + v.x j i :=
      calc
        ∑ k : Fin p.n, v.x j k ≥
            ∑ k ∈ ({0, i} : Finset (Fin p.n)), v.x j k :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _)
            (fun k _ _ => xnn h j k)
        _ = v.x j 0 + v.x j i := sum_pair h0i
    omega
  have hpairR : (v.x j 0 : ℝ) + (v.x j i : ℝ) ≤ 1 := by
    exact_mod_cast hpairZ
  have hpot : v.u j - v.u i - 1 ≤ (p.n : ℝ) - 3 := by
    have hhi := h.hu_hi j
    have hlo := h.hu_lo i hi
    linarith
  have hnR : (4 : ℝ) ≤ p.n := by exact_mod_cast hn
  rcases h.hx_bin 0 i with hx0i | hx0i
  · rcases h.hx_bin i j with hxij | hxij
    · rw [hx0i, hxij]
      push_cast
      nlinarith
    · rw [hx0i, hxij]
      push_cast
      nlinarith
  · rcases h.hx_bin i j with hxij | hxij
    · rw [hx0i, hxij]
      push_cast
      nlinarith
    · have hui := u_eq_2_of_arc_from_depot h hi hx0i
      have huj := arc_consec_nondepot h hj hi hxij
      have hxji : v.x j i = 0 := by
        apply (h.hx_bin j i).resolve_right
        intro hxji
        obtain ⟨k, hk, huniq⟩ := exists_unique_in h i
        have h0k : (0 : Fin p.n) = k := huniq 0 hx0i
        have hjk : j = k := huniq j hxji
        have h0j : (0 : Fin p.n) = j := h0k.trans hjk.symm
        exact hj (by rw [← h0j]; rfl)
      have hxj0 : v.x j 0 = 0 := by
        apply (h.hx_bin j 0).resolve_right
        intro hxj0
        have hujn := u_eq_n_of_arc_to_depot h hj hxj0
        nlinarith
      rw [hx0i, hxij, hxji, hxj0, hui, huj]
      push_cast
      rw [hui]
      norm_num

private lemma adFwdFeas (p : P12.a.Params) (v : P12.a.Vars p)
    (h : P12.a.Feasible p v) :
    P12.d.Feasible (adParamMap p) (adFwd p v) := by
  by_cases hn : p.n = 3
  · by_cases hx : v.x ⟨0, by omega⟩ ⟨1, by omega⟩ = 1
    · let hq : adTargetParams4 p hn = adParamMap p := by
        simp [adParamMap, hn]
      simpa [adFwd, hn, hx] using
        adDFeasibleCast hq (adTargetTourA p hn) (adTargetTourAFeasible p hn)
    · let hq : adTargetParams4 p hn = adParamMap p := by
        simp [adParamMap, hn]
      simpa [adFwd, hn, hx] using
        adDFeasibleCast hq (adTargetTourB p hn) (adTargetTourBFeasible p hn)
  · let q : P12.d.Params := { n := p.n, c := p.c, hn := p.hn }
    let w : P12.d.Vars q := { x := v.x, u := v.u }
    have hec3 :
        ∀ (i j : Fin p.n), i.val ≠ 0 → j.val ≠ 0 → i ≠ j →
          haveI : NeZero p.n := ⟨by have := p.hn; omega⟩
          (v.x j 0 : ℝ) + (v.x j i : ℝ) + (v.u j - v.u i - 1) ≤
            ((p.n : ℝ) - 1) *
              (2 - (v.x 0 i : ℝ) - (v.x i j : ℝ)) := by
      intro i j hi hj hij
      by_cases hn2 : p.n = 2
      · exfalso
        apply hij
        apply Fin.ext
        have hil := i.isLt
        have hjl := j.isLt
        omega
      · exact adEC3OfLarge p v h (by omega) i j hi hj hij
    have hw : P12.d.Feasible q w :=
      { hout := h.hout
        hin := h.hin
        hmtz := h.hmtz
        hu_depot := h.hu_depot
        hx_bin := h.hx_bin
        hu_lo := h.hu_lo
        hu_hi := h.hu_hi
        hec3 := hec3
        hx_no_self := h.hx_no_self }
    let hq : q = adParamMap p := by
      simp [q, adParamMap, hn]
    simpa [adFwd, hn, q, w] using adDFeasibleCast hq w hw

private lemma adBwdFeas (p : P12.a.Params)
    (v : P12.d.Vars (adParamMap p))
    (h : P12.d.Feasible (adParamMap p) v) :
    P12.a.Feasible p (adBwd p v) := by
  by_cases hn : p.n = 3
  · let w : P12.d.Vars (adTargetParams4 p hn) :=
      cast (by simp [adParamMap, hn]) v
    by_cases hx :
        w.x ⟨0, by simp [adTargetParams4]⟩
          ⟨2, by simp [adTargetParams4]⟩ = 1
    · have hbwd : adBwd p v = adSourceTourB p := by
        simp only [adBwd, dif_pos hn]
        rw [if_pos (by simpa [w] using hx)]
      rw [hbwd]
      exact adSourceTourBFeasible p hn
    · have hbwd : adBwd p v = adSourceTourA p := by
        simp only [adBwd, dif_pos hn]
        rw [if_neg (by simpa [w] using hx)]
      rw [hbwd]
      exact adSourceTourAFeasible p hn
  · let q : P12.d.Params := { n := p.n, c := p.c, hn := p.hn }
    let hq : adParamMap p = q := by
      simp [q, adParamMap, hn]
    let w : P12.d.Vars q := cast (congrArg P12.d.Vars hq) v
    have hw : P12.d.Feasible q w := adDFeasibleCast hq v h
    simp only [adBwd, dif_neg hn]
    exact
      { hout := hw.hout
        hin := hw.hin
        hmtz := hw.hmtz
        hu_depot := hw.hu_depot
        hx_bin := hw.hx_bin
        hu_lo := hw.hu_lo
        hu_hi := hw.hu_hi
        hx_no_self := hw.hx_no_self }

private lemma adBwdFwd (p : P12.a.Params) (v : P12.a.Vars p)
    (h : P12.a.Feasible p v) :
    adBwd p (adFwd p v) = v := by
  by_cases hn : p.n = 3
  · by_cases hx : v.x ⟨0, by omega⟩ ⟨1, by omega⟩ = 1
    · rw [show adBwd p (adFwd p v) = adSourceTourA p by
        simp [adBwd, adFwd, adParamMap, adTargetParams4, adTargetTourA, hn, hx]]
      exact adSourceEqTourA p v h hn hx
    · rw [show adBwd p (adFwd p v) = adSourceTourB p by
        simp [adBwd, adFwd, adParamMap, adTargetParams4, adTargetTourB, hn, hx]]
      exact adSourceEqTourB p v h hn hx
  · simp [adBwd, adFwd, adParamMap, hn]

private lemma adSourceObjA (p : P12.a.Params) (hn : p.n = 3) :
    P12.a.obj p (adSourceTourA p) = adGammaA p hn := by
  rcases p with ⟨n, c, hp⟩
  simp only at hn
  subst n
  change
    (∑ i : Fin 3, ∑ j : Fin 3,
      c i j * ((adSourceTourA { n := 3, c := c, hn := hp }).x i j : ℝ)) =
        c 0 1 + c 1 2 + c 2 0
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three,
    Fin.sum_univ_three]
  norm_num [adSourceTourA]
  split_ifs with hzero
  · have hval := congrArg Fin.val hzero
    norm_num at hval
  · ring

private lemma adSourceObjB (p : P12.a.Params) (hn : p.n = 3) :
    P12.a.obj p (adSourceTourB p) = adGammaB p hn := by
  rcases p with ⟨n, c, hp⟩
  simp only at hn
  subst n
  change
    (∑ i : Fin 3, ∑ j : Fin 3,
      c i j * ((adSourceTourB { n := 3, c := c, hn := hp }).x i j : ℝ)) =
        c 0 2 + c 2 1 + c 1 0
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three,
    Fin.sum_univ_three]
  norm_num [adSourceTourB]
  split_ifs with hzero
  · have hval := congrArg Fin.val hzero
    norm_num at hval
  · ring

private lemma adTargetObj (p : P12.a.Params) (hn : p.n = 3)
    (v : P12.d.Vars (adTargetParams4 p hn))
    (h : P12.d.Feasible (adTargetParams4 p hn) v) :
    P12.d.obj (adTargetParams4 p hn) v =
      if v.x ⟨0, by simp [adTargetParams4]⟩
          ⟨2, by simp [adTargetParams4]⟩ = 1 then
        adGammaB p hn
      else
        adGammaA p hn := by
  have hs := h.hout ⟨0, by simp [adTargetParams4]⟩
  change
    (∑ j : Fin 4,
      v.x ⟨0, by simp [adTargetParams4]⟩ j) = 1 at hs
  rw [Fin.sum_univ_four] at hs
  change
    v.x ⟨0, by simp [adTargetParams4]⟩
        ⟨0, by simp [adTargetParams4]⟩ +
      v.x ⟨0, by simp [adTargetParams4]⟩
        ⟨1, by simp [adTargetParams4]⟩ +
      v.x ⟨0, by simp [adTargetParams4]⟩
        ⟨2, by simp [adTargetParams4]⟩ +
      v.x ⟨0, by simp [adTargetParams4]⟩
        ⟨3, by simp [adTargetParams4]⟩ = 1 at hs
  have hself := h.hx_no_self ⟨0, by simp [adTargetParams4]⟩
  change
    v.x ⟨0, by simp [adTargetParams4]⟩
      ⟨0, by simp [adTargetParams4]⟩ = 0 at hself
  let i0 : Fin (adTargetParams4 p hn).n := ⟨0, by simp [adTargetParams4]⟩
  let i1 : Fin (adTargetParams4 p hn).n := ⟨1, by simp [adTargetParams4]⟩
  let i2 : Fin (adTargetParams4 p hn).n := ⟨2, by simp [adTargetParams4]⟩
  let i3 : Fin (adTargetParams4 p hn).n := ⟨3, by simp [adTargetParams4]⟩
  change
    (∑ i : Fin 4, ∑ j : Fin 4,
      (if i.val = 0 then
        if j.val = 2 then adGammaB p hn else adGammaA p hn
      else 0) * (v.x i j : ℝ)) =
        if v.x i0 i2 = 1 then adGammaB p hn else adGammaA p hn
  rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four,
    Fin.sum_univ_four, Fin.sum_univ_four]
  norm_num
  change
    adGammaA p hn * (v.x i0 i0 : ℝ) +
        adGammaA p hn * (v.x i0 i1 : ℝ) +
        adGammaB p hn * (v.x i0 i2 : ℝ) +
        adGammaA p hn * (v.x i0 i3 : ℝ) =
      if v.x i0 i2 = 1 then adGammaB p hn else adGammaA p hn
  change v.x i0 i0 + v.x i0 i1 + v.x i0 i2 + v.x i0 i3 = 1 at hs
  change v.x i0 i0 = 0 at hself
  by_cases hx2 : v.x i0 i2 = 1
  · rw [if_pos hx2]
    have hx1 : v.x i0 i1 = 0 := by
      rcases h.hx_bin i0 i1 with h0 | h1
      · exact h0
      · rcases h.hx_bin i0 i3 with h30 | h31 <;> omega
    have hx3 : v.x i0 i3 = 0 := by
      rcases h.hx_bin i0 i3 with h0 | h1
      · exact h0
      · rcases h.hx_bin i0 i1 with h10 | h11 <;> omega
    rw [hself, hx1, hx2, hx3]
    norm_num
  · rw [if_neg hx2]
    have hx20 : v.x i0 i2 = 0 := (h.hx_bin i0 i2).resolve_right hx2
    have hs' :
        (v.x i0 i0 : ℝ) + (v.x i0 i1 : ℝ) +
            (v.x i0 i2 : ℝ) + (v.x i0 i3 : ℝ) = 1 := by
      exact_mod_cast hs
    rw [hself, hx20] at hs'
    rw [hself, hx20]
    push_cast at hs'
    have hsum : (v.x i0 i1 : ℝ) + (v.x i0 i3 : ℝ) = 1 := by
      linarith
    norm_num
    calc
      adGammaA p hn * (v.x i0 i1 : ℝ) +
          adGammaA p hn * (v.x i0 i3 : ℝ) =
          adGammaA p hn *
            ((v.x i0 i1 : ℝ) + (v.x i0 i3 : ℝ)) := by ring
      _ = adGammaA p hn := by rw [hsum]; ring

private lemma adFwdObj (p : P12.a.Params) (v : P12.a.Vars p)
    (h : P12.a.Feasible p v) :
    P12.d.obj (adParamMap p) (adFwd p v) = P12.a.obj p v := by
  by_cases hn : p.n = 3
  · let hq : adTargetParams4 p hn = adParamMap p := by
      simp [adParamMap, hn]
    by_cases hx : v.x ⟨0, by omega⟩ ⟨1, by omega⟩ = 1
    · have hv := adSourceEqTourA p v h hn hx
      calc
        P12.d.obj (adParamMap p) (adFwd p v) =
            P12.d.obj (adTargetParams4 p hn) (adTargetTourA p hn) := by
          rw [show adFwd p v =
              cast (congrArg P12.d.Vars hq) (adTargetTourA p hn) by
            simp [adFwd, hn, hx]]
          exact adDObjCast hq (adTargetTourA p hn)
        _ = adGammaA p hn := by
          rw [adTargetObj p hn _ (adTargetTourAFeasible p hn)]
          simp [adTargetTourA, adTargetParams4]
        _ = P12.a.obj p v := by
          rw [← hv]
          exact (adSourceObjA p hn).symm
    · have hv := adSourceEqTourB p v h hn hx
      calc
        P12.d.obj (adParamMap p) (adFwd p v) =
            P12.d.obj (adTargetParams4 p hn) (adTargetTourB p hn) := by
          rw [show adFwd p v =
              cast (congrArg P12.d.Vars hq) (adTargetTourB p hn) by
            simp [adFwd, hn, hx]]
          exact adDObjCast hq (adTargetTourB p hn)
        _ = adGammaB p hn := by
          rw [adTargetObj p hn _ (adTargetTourBFeasible p hn)]
          simp [adTargetTourB, adTargetParams4]
        _ = P12.a.obj p v := by
          rw [← hv]
          exact (adSourceObjB p hn).symm
  · let q : P12.d.Params := { n := p.n, c := p.c, hn := p.hn }
    let w : P12.d.Vars q := { x := v.x, u := v.u }
    let hq : q = adParamMap p := by
      simp [q, adParamMap, hn]
    rw [show adFwd p v = cast (congrArg P12.d.Vars hq) w by
      simp [adFwd, hn, q, w]]
    rw [adDObjCast hq]
    rfl

private lemma adBwdObj (p : P12.a.Params)
    (v : P12.d.Vars (adParamMap p))
    (h : P12.d.Feasible (adParamMap p) v) :
    P12.d.obj (adParamMap p) v = P12.a.obj p (adBwd p v) := by
  by_cases hn : p.n = 3
  · let hq : adParamMap p = adTargetParams4 p hn := by
      simp [adParamMap, hn]
    let w : P12.d.Vars (adTargetParams4 p hn) :=
      cast (congrArg P12.d.Vars hq) v
    have hw : P12.d.Feasible (adTargetParams4 p hn) w :=
      adDFeasibleCast hq v h
    by_cases hx :
        w.x ⟨0, by simp [adTargetParams4]⟩
          ⟨2, by simp [adTargetParams4]⟩ = 1
    · rw [← adDObjCast hq v, adTargetObj p hn w hw, if_pos hx]
      have hbwd : adBwd p v = adSourceTourB p := by
        simp only [adBwd, dif_pos hn]
        rw [if_pos (by simpa [w] using hx)]
      rw [hbwd]
      exact (adSourceObjB p hn).symm
    · rw [← adDObjCast hq v, adTargetObj p hn w hw, if_neg hx]
      have hbwd : adBwd p v = adSourceTourA p := by
        simp only [adBwd, dif_pos hn]
        rw [if_neg (by simpa [w] using hx)]
      rw [hbwd]
      exact (adSourceObjA p hn).symm
  · let q : P12.d.Params := { n := p.n, c := p.c, hn := p.hn }
    let hq : adParamMap p = q := by
      simp [q, adParamMap, hn]
    let w : P12.d.Vars q := cast (congrArg P12.d.Vars hq) v
    rw [← adDObjCast hq v]
    rw [show adBwd p v = { x := w.x, u := w.u } by
      simp [adBwd, hn, w, q]]
    change P12.d.obj q w = P12.a.obj p { x := w.x, u := w.u }
    rfl

/-- With an unrestricted parameter mapping, the EC3 augmentation is a section
reformulation. Three-city source instances are redirected to four-city target
instances whose depot-outgoing costs encode the two source-tour objectives;
all other instance sizes are copied unchanged. -/
noncomputable def aDReformulation :
    MILPReformulation P12.a.formulation P12.d.formulation where
  paramMap := adParamMap
  fwd := adFwd
  bwd := adBwd
  fwd_feas := adFwdFeas
  bwd_feas := adBwdFeas
  bwd_fwd := adBwdFwd
  objMap := id
  objMap_mono := strictMono_id
  fwd_obj := adFwdObj
  bwd_obj := adBwdObj

end P12
