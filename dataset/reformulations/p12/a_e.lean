import Common
import problems.p12.formulations.a.Formulation
import problems.p12.formulations.e.Formulation
import Mathlib.Tactic

open BigOperators Finset

namespace P12

-- ============================================================================
-- § Parameter Mapping
-- ============================================================================

/-- The identity parameter mapping from formulation `a` to formulation `e`.
The two parameter types are structurally identical but distinct, so the
identity has to be written out field by field. -/
def paramMapAE (p : P12.a.Params) : P12.e.Params :=
  { n  := p.n
    c  := p.c
    hn := p.hn }

-- ============================================================================
-- § Witness Instance
-- ============================================================================

/-- The degenerate 2-city instance used as the witness (source side). -/
private abbrev p2 : P12.a.Params :=
  ⟨2, fun _ _ => 0, le_refl 2⟩

/-- The same instance on the target side (`= paramMapAE p2`, definitionally). -/
private abbrev q2 : P12.e.Params :=
  ⟨2, fun _ _ => 0, le_refl 2⟩

/-- The unique tour `0 → 1 → 0`, feasible for formulation `a` at `p2`. -/
private def tour2 : P12.a.Vars p2 :=
  { x := fun i j => if i = j then 0 else 1
    u := fun i => if i.val = 0 then 1 else 2 }

private lemma tour2_feasible : P12.a.Feasible p2 tour2 := by
  refine
    { hout := ?_, hin := ?_, hmtz := ?_, hu_depot := ?_, hx_bin := ?_,
      hu_lo := ?_, hu_hi := ?_, hx_no_self := ?_ }
  · intro i; fin_cases i <;> simp [tour2, Fin.sum_univ_two]
  · intro j; fin_cases j <;> simp [tour2, Fin.sum_univ_two]
  · intro i j hi hj hij; fin_cases i <;> fin_cases j <;> simp_all
  · simp [tour2]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [tour2]
  · intro i hi; fin_cases i <;> simp_all [tour2]
  · intro i; fin_cases i <;> norm_num [tour2]
  · intro i; fin_cases i <;> simp [tour2]

/-- Any point feasible for formulation `e` at the 2-city instance violates the
EC1 cut: the two arcs `0 → 1` and `1 → 0` are both forced active, so
`x₀₁ + x₁₀ = 2 ≤ 1`. Hence the `e`-feasible set at this instance is empty. -/
private lemma e_infeasible (w : P12.e.Vars q2)
    (h : P12.e.Feasible q2 w) : False := by
  have h01 : w.x 0 1 = 1 := by
    have hs := h.hout 0
    rw [Fin.sum_univ_two] at hs
    have := h.hx_no_self 0
    omega
  have h10 : w.x 1 0 = 1 := by
    have hs := h.hout 1
    rw [Fin.sum_univ_two] at hs
    have := h.hx_no_self 1
    omega
  have hcut := h.hec1 0 1 (by decide)
  omega

-- ============================================================================
-- § Disproof
-- ============================================================================

/-- Formulation `e` (MTZ augmented with the EC1 cut of EvoCut v2) is **not** a
reformulation of formulation `a` (MTZ) under the identity parameter mapping: no
`MILPReformulation` whose `paramMap` is `paramMapAE` can exist.

Witness: the 2-city instance. Its `a`-feasible set is the single tour
`0 → 1 → 0`, with `x 0 1 = x 1 0 = 1` and potentials `u 0 = 1`, `u 1 = 2`. At
`i = 0`, `j = 1` the cut reduces to `2 ≤ 1`, so this unique feasible point is
removed and the `e`-feasible set is empty. Pushing the `a`-feasible tour through
`Φ.fwd` therefore lands in the empty `e`-feasible set — a contradiction. This is
the constructive form of the cardinality obstruction `MILPReformulation.fwd_injOn`.

Pinning the parameter mapping is necessary: the cut is valid on every instance
with `n ≥ 3` (a violation would require the 2-cycle `x i j = x j i = 1`), so an
unrestricted parameter mapping is free to redirect the degenerate size `n = 2`
to a larger instance on which the cut is inert, and a reformulation does then
exist. -/
theorem not_aEReformulation
    (Φ : MILPReformulation P12.a.formulation P12.e.formulation)
    (hΦ : Φ.paramMap = paramMapAE) : False := by
  obtain ⟨paramMap, fwd, _, fwd_feas, _⟩ := Φ
  subst hΦ
  exact e_infeasible _ (fwd_feas p2 tour2 tour2_feasible)

-- ============================================================================
-- § Unrestricted Parameter Mapping
-- ============================================================================

private lemma pathExistsUniqueOut {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) (i : Fin p.n) :
    ∃! k, v.x i k = 1 := by
  have hsum := h.hout i
  have hex : ∃ k, v.x i k = 1 := by
    by_contra hc
    push_neg at hc
    have h0 : ∀ k, v.x i k = 0 := fun k =>
      (h.hx_bin i k).resolve_right (hc k)
    simp [h0] at hsum
  obtain ⟨k, hk⟩ := hex
  refine ⟨k, hk, fun k' hk' => ?_⟩
  by_contra hne
  have hnonneg : ∀ j, 0 ≤ v.x i j := fun j => by
    rcases h.hx_bin i j with hj | hj <;> omega
  have hge : ∑ j, v.x i j ≥ v.x i k + v.x i k' :=
    calc
      ∑ j, v.x i j ≥ ∑ j ∈ ({k, k'} : Finset (Fin p.n)), v.x i j :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _ => hnonneg j)
      _ = v.x i k + v.x i k' := sum_pair (Ne.symm hne)
  omega

private noncomputable def pathSucc {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) (i : Fin p.n) : Fin p.n :=
  (pathExistsUniqueOut h i).choose

private lemma pathSuccSpec {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) (i : Fin p.n) :
    v.x i (pathSucc h i) = 1 :=
  (pathExistsUniqueOut h i).choose_spec.1

private lemma pathSuccUnique {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) (i k : Fin p.n) (hk : v.x i k = 1) :
    k = pathSucc h i := by
  obtain ⟨w, hw, huniq⟩ := pathExistsUniqueOut h i
  have hk' : k = w := huniq k hk
  have hs' : pathSucc h i = w := huniq (pathSucc h i) (pathSuccSpec h i)
  exact hk'.trans hs'.symm

private lemma pathSuccInjective {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) : Function.Injective (pathSucc h) := by
  intro i i' hii'
  have hi := pathSuccSpec h i
  have hi' := pathSuccSpec h i'
  rw [hii'] at hi
  by_contra hne
  have hnonneg : ∀ j, 0 ≤ v.x j (pathSucc h i') := fun j => by
    rcases h.hx_bin j (pathSucc h i') with hj | hj <;> omega
  have hge :
      ∑ j, v.x j (pathSucc h i') ≥
        v.x i (pathSucc h i') + v.x i' (pathSucc h i') :=
    calc
      ∑ j, v.x j (pathSucc h i') ≥
          ∑ j ∈ ({i, i'} : Finset (Fin p.n)), v.x j (pathSucc h i') :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _ => hnonneg j)
      _ = v.x i (pathSucc h i') + v.x i' (pathSucc h i') := sum_pair hne
  have hsum := h.hin (pathSucc h i')
  omega

private lemma pathSuccNeSelf {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) (i : Fin p.n) : pathSucc h i ≠ i := by
  intro hi
  have hs := pathSuccSpec h i
  rw [hi, h.hx_no_self] at hs
  omega

private lemma pathPosIncrease {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) {i : Fin p.n} (hi : i.val ≠ 0)
    (hsi : (pathSucc h i).val ≠ 0) :
    v.u i + 1 ≤ v.u (pathSucc h i) := by
  have hx := pathSuccSpec h i
  have hmtz := h.hmtz i (pathSucc h i) hi hsi (pathSuccNeSelf h i).symm
  have hx' : (v.x i (pathSucc h i) : ℝ) = 1 := by exact_mod_cast hx
  nlinarith

private lemma pathPosIterateIncrease {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) {m : Fin p.n} (_hm : m.val ≠ 0) {k : ℕ}
    (hall : ∀ i : ℕ, i ≤ k → ((pathSucc h)^[i] m).val ≠ 0) :
    v.u m + k ≤ v.u ((pathSucc h)^[k] m) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hall' : ∀ i, i ≤ k → ((pathSucc h)^[i] m).val ≠ 0 :=
      fun i hi => hall i (by omega)
    have hk := hall k (Nat.le_succ k)
    have hsk := hall (k + 1) le_rfl
    have hih := ih hall'
    rw [Function.iterate_succ', Function.comp_apply]
    rw [Function.iterate_succ', Function.comp_apply] at hsk
    have hstep := pathPosIncrease h hk hsk
    push_cast
    linarith

private lemma pathReachesDepot {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) (m : Fin p.n) :
    ∃ k : ℕ, ((pathSucc h)^[k] m).val = 0 := by
  by_contra hc
  push_neg at hc
  have hm : m.val ≠ 0 := hc 0
  have hgrow :=
    pathPosIterateIncrease h hm (k := p.n) (fun i _ => hc i)
  have hbound := h.hu_hi ((pathSucc h)^[p.n] m)
  have hlo := h.hu_lo m hm
  linarith

private lemma pathNoTwoCycle {p : P12.a.Params} {v : P12.a.Vars p}
    (h : P12.a.Feasible p v) (hn : p.n ≠ 2)
    (i j : Fin p.n) (hij : i < j) :
    v.x i j + v.x j i ≤ 1 := by
  haveI : NeZero p.n := ⟨by have := p.hn; omega⟩
  rcases h.hx_bin i j with hij0 | hij1
  · rcases h.hx_bin j i with hji0 | hji1 <;> omega
  rcases h.hx_bin j i with hji0 | hji1
  · omega
  have hj0 : j.val ≠ 0 := by omega
  by_cases hi0 : i.val = 0
  · have hi : i = 0 := by
      apply Fin.ext
      simpa using hi0
    subst i
    have hs0 : pathSucc h 0 = j := (pathSuccUnique h 0 j hij1).symm
    have hsj : pathSucc h j = 0 := (pathSuccUnique h j 0 hji1).symm
    have hn3 : 3 ≤ p.n := by omega
    let m : Fin p.n :=
      if hj : j.val = 1 then ⟨2, by omega⟩ else ⟨1, by omega⟩
    have hm0 : m ≠ 0 := by
      by_cases hj : j.val = 1 <;> simp [m, hj]
    have hmj : m ≠ j := by
      by_cases hj : j.val = 1
      · intro hm
        have hmval := congrArg Fin.val hm
        simp [m, hj] at hmval
      · intro hm
        have hmval := congrArg Fin.val hm
        simp [m, hj] at hmval
        exact hj hmval.symm
    obtain ⟨q, hq⟩ := pathReachesDepot h m
    have horbit :
        ∀ q : ℕ, ∃ z : Fin p.n,
          (z = 0 ∨ z = j) ∧ ((pathSucc h)^[q] z).val = 0 := by
      intro r
      induction r with
      | zero => exact ⟨0, Or.inl rfl, by simp⟩
      | succ r ihr =>
        obtain ⟨z, hz, hz0⟩ := ihr
        rcases hz with rfl | rfl
        · refine ⟨j, Or.inr rfl, ?_⟩
          rw [Function.iterate_succ_apply, hsj]
          exact hz0
        · refine ⟨0, Or.inl rfl, ?_⟩
          rw [Function.iterate_succ_apply, hs0]
          exact hz0
    obtain ⟨z, hz, hz0⟩ := horbit q
    have hiter :
        Function.Injective ((pathSucc h)^[q]) :=
      (pathSuccInjective h).iterate q
    have hmz : m = z := by
      apply hiter
      apply Fin.ext
      exact hq.trans hz0.symm
    rcases hz with rfl | rfl
    · exfalso
      exact hm0 hmz
    · exfalso
      exact hmj hmz
  · have hmtz1 := h.hmtz i j hi0 hj0 (ne_of_lt hij)
    have hmtz2 := h.hmtz j i hj0 hi0 (ne_of_gt hij)
    have hij1' : (v.x i j : ℝ) = 1 := by exact_mod_cast hij1
    have hji1' : (v.x j i : ℝ) = 1 := by exact_mod_cast hji1
    nlinarith

private def pathBaseCost (p : P12.a.Params) : ℝ :=
  p.c ⟨0, by have := p.hn; omega⟩ ⟨1, by have := p.hn; omega⟩ +
    p.c ⟨1, by have := p.hn; omega⟩ ⟨0, by have := p.hn; omega⟩

private def pathParams3 (p : P12.a.Params) : P12.e.Params :=
  { n := 3
    c := fun i _ => if i.val = 0 then pathBaseCost p else 0
    hn := by omega }

private def pathologicalParamMapAE (p : P12.a.Params) : P12.e.Params :=
  if p.n = 2 then
    pathParams3 p
  else
    { n := p.n
      c := p.c
      hn := p.hn }

private def pathTour3 (p : P12.a.Params) : P12.e.Vars (pathParams3 p) :=
  { x := fun i j =>
      if (i.val = 0 ∧ j.val = 1) ∨
          (i.val = 1 ∧ j.val = 2) ∨
          (i.val = 2 ∧ j.val = 0) then 1 else 0
    u := fun i => i.val + 1 }

private def pathTour2 (p : P12.a.Params) : P12.a.Vars p :=
  { x := fun i j => if i = j then 0 else 1
    u := fun i => if i.val = 0 then 1 else 2 }

private def pathologicalFwdAE (p : P12.a.Params) (v : P12.a.Vars p) :
    P12.e.Vars (pathologicalParamMapAE p) :=
  if hn : p.n = 2 then
    cast (by simp [pathologicalParamMapAE, hn]) (pathTour3 p)
  else
    cast (by simp [pathologicalParamMapAE, hn])
      ({ x := v.x, u := v.u } :
        P12.e.Vars { n := p.n, c := p.c, hn := p.hn })

private def pathologicalBwdAE (p : P12.a.Params)
    (v : P12.e.Vars (pathologicalParamMapAE p)) : P12.a.Vars p :=
  if hn : p.n = 2 then
    pathTour2 p
  else
    let v' : P12.e.Vars { n := p.n, c := p.c, hn := p.hn } :=
      cast (by simp [pathologicalParamMapAE, hn]) v
    { x := v'.x, u := v'.u }

private lemma pathEFeasibleCast {q q' : P12.e.Params} (hq : q = q')
    (v : P12.e.Vars q) (h : P12.e.Feasible q v) :
    P12.e.Feasible q' (cast (congrArg P12.e.Vars hq) v) := by
  subst q'
  simpa

private lemma pathEObjCast {q q' : P12.e.Params} (hq : q = q')
    (v : P12.e.Vars q) :
    P12.e.obj q' (cast (congrArg P12.e.Vars hq) v) = P12.e.obj q v := by
  subst q'
  rfl

private lemma pathTour3Feasible (p : P12.a.Params) (hn : p.n = 2) :
    P12.e.Feasible (pathParams3 p) (pathTour3 p) := by
  rcases p with ⟨n, c, hp⟩
  simp only at hn
  subst n
  refine
    { hout := ?_, hin := ?_, hmtz := ?_, hu_depot := ?_, hx_bin := ?_,
      hu_lo := ?_, hu_hi := ?_, hec1 := ?_, hx_no_self := ?_ }
  · intro i
    change ∑ j : Fin 3, (if
      (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 2) ∨
        (i.val = 2 ∧ j.val = 0) then 1 else 0) = 1
    fin_cases i <;> rw [Fin.sum_univ_three] <;> norm_num
  · intro j
    change ∑ i : Fin 3, (if
      (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 2) ∨
        (i.val = 2 ∧ j.val = 0) then 1 else 0) = 1
    fin_cases j <;> rw [Fin.sum_univ_three] <;> norm_num
  · intro i j hi hj hij
    fin_cases i <;> fin_cases j <;>
      norm_num [pathTour3, pathParams3] at *
  · norm_num [pathTour3, pathParams3]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pathTour3, pathParams3]
  · intro i hi
    fin_cases i <;> norm_num [pathTour3, pathParams3] at *
  · intro i
    fin_cases i <;> norm_num [pathTour3, pathParams3]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [pathTour3, pathParams3] at *
  · intro i
    fin_cases i <;> norm_num [pathTour3, pathParams3]

private lemma pathTour2Feasible (p : P12.a.Params) (hn : p.n = 2) :
    P12.a.Feasible p (pathTour2 p) := by
  rcases p with ⟨n, c, hp⟩
  simp only at hn
  subst n
  refine
    { hout := ?_, hin := ?_, hmtz := ?_, hu_depot := ?_, hx_bin := ?_,
      hu_lo := ?_, hu_hi := ?_, hx_no_self := ?_ }
  · intro i
    fin_cases i <;> simp [pathTour2, Fin.sum_univ_two]
  · intro j
    fin_cases j <;> simp [pathTour2, Fin.sum_univ_two]
  · intro i j hi hj hij
    fin_cases i <;> fin_cases j <;> simp_all
  · simp [pathTour2]
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [pathTour2]
  · intro i hi
    fin_cases i <;> simp_all [pathTour2]
  · intro i
    fin_cases i <;> norm_num [pathTour2]
  · intro i
    fin_cases i <;> simp [pathTour2]

private lemma pathologicalFwdFeasAE (p : P12.a.Params) (v : P12.a.Vars p)
    (h : P12.a.Feasible p v) :
    P12.e.Feasible (pathologicalParamMapAE p) (pathologicalFwdAE p v) := by
  by_cases hn : p.n = 2
  · let hq : pathParams3 p = pathologicalParamMapAE p := by
      simp [pathologicalParamMapAE, hn]
    simpa [pathologicalFwdAE, hn] using
      pathEFeasibleCast hq (pathTour3 p) (pathTour3Feasible p hn)
  · let q : P12.e.Params := { n := p.n, c := p.c, hn := p.hn }
    let w : P12.e.Vars q := { x := v.x, u := v.u }
    have hw : P12.e.Feasible q w :=
      { hout := h.hout
        hin := h.hin
        hmtz := h.hmtz
        hu_depot := h.hu_depot
        hx_bin := h.hx_bin
        hu_lo := h.hu_lo
        hu_hi := h.hu_hi
        hec1 := pathNoTwoCycle h hn
        hx_no_self := h.hx_no_self }
    let hq : q = pathologicalParamMapAE p := by
      simp [q, pathologicalParamMapAE, hn]
    simpa [pathologicalFwdAE, hn, q, w] using pathEFeasibleCast hq w hw

private lemma pathologicalBwdFeasAE (p : P12.a.Params)
    (v : P12.e.Vars (pathologicalParamMapAE p))
    (h : P12.e.Feasible (pathologicalParamMapAE p) v) :
    P12.a.Feasible p (pathologicalBwdAE p v) := by
  by_cases hn : p.n = 2
  · simpa only [pathologicalBwdAE, dif_pos hn] using pathTour2Feasible p hn
  · let q : P12.e.Params := { n := p.n, c := p.c, hn := p.hn }
    let hq : pathologicalParamMapAE p = q := by
      simp [q, pathologicalParamMapAE, hn]
    let w : P12.e.Vars q :=
      cast (congrArg P12.e.Vars hq) v
    have hw : P12.e.Feasible q w := pathEFeasibleCast hq v h
    simp only [pathologicalBwdAE, dif_neg hn]
    exact
      { hout := hw.hout
        hin := hw.hin
        hmtz := hw.hmtz
        hu_depot := hw.hu_depot
        hx_bin := hw.hx_bin
        hu_lo := hw.hu_lo
        hu_hi := hw.hu_hi
        hx_no_self := hw.hx_no_self }

private lemma pathSourceUnique (p : P12.a.Params) (v : P12.a.Vars p)
    (h : P12.a.Feasible p v) (hn : p.n = 2) :
    pathTour2 p = v := by
  rcases p with ⟨n, c, hp⟩
  simp only at hn
  subst n
  cases v with
  | mk x u =>
    unfold pathTour2
    rw [P12.a.Vars.mk.injEq]
    constructor
    · funext i j
      fin_cases i <;> fin_cases j
      · simpa using (h.hx_no_self 0).symm
      · have hs := h.hout 0
        rw [Fin.sum_univ_two, h.hx_no_self] at hs
        simpa using hs.symm
      · have hs := h.hout 1
        rw [Fin.sum_univ_two, h.hx_no_self] at hs
        simpa using hs.symm
      · simpa using (h.hx_no_self 1).symm
    · funext i
      fin_cases i
      · simpa using h.hu_depot.symm
      · have hlo := h.hu_lo 1 (by norm_num)
        have hhi := h.hu_hi 1
        norm_num at hhi
        exact le_antisymm hlo hhi

private lemma pathologicalBwdFwdAE (p : P12.a.Params) (v : P12.a.Vars p)
    (h : P12.a.Feasible p v) :
    pathologicalBwdAE p (pathologicalFwdAE p v) = v := by
  by_cases hn : p.n = 2
  · simpa only [pathologicalBwdAE, dif_pos hn] using
      pathSourceUnique p v h hn
  · simp [pathologicalBwdAE, pathologicalFwdAE, pathologicalParamMapAE, hn]

private lemma pathSourceObj (p : P12.a.Params) (v : P12.a.Vars p)
    (h : P12.a.Feasible p v) (hn : p.n = 2) :
    P12.a.obj p v = pathBaseCost p := by
  rw [← pathSourceUnique p v h hn]
  rcases p with ⟨n, c, hp⟩
  simp only at hn
  subst n
  change (∑ i : Fin 2, ∑ j : Fin 2,
    c i j * ((pathTour2 { n := 2, c := c, hn := hp }).x i j : ℝ)) =
      c 0 1 + c 1 0
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num [pathTour2]

private lemma pathTargetObj (p : P12.a.Params)
    (v : P12.e.Vars (pathParams3 p))
    (h : P12.e.Feasible (pathParams3 p) v) :
    P12.e.obj (pathParams3 p) v = pathBaseCost p := by
  haveI : NeZero (pathParams3 p).n := ⟨by simp [pathParams3]⟩
  have hs := h.hout 0
  change (∑ j : Fin 3, v.x 0 j) = 1 at hs
  rw [Fin.sum_univ_three] at hs
  change
    (∑ i : Fin 3, ∑ j : Fin 3,
      (if i.val = 0 then pathBaseCost p else 0) * (v.x i j : ℝ)) =
        pathBaseCost p
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three,
    Fin.sum_univ_three]
  norm_num
  rw [← mul_add, ← mul_add]
  have hs' : (v.x 0 0 : ℝ) + (v.x 0 1 : ℝ) + (v.x 0 2 : ℝ) = 1 := by
    exact_mod_cast hs
  rw [hs', mul_one]

private lemma pathologicalFwdObjAE (p : P12.a.Params) (v : P12.a.Vars p)
    (h : P12.a.Feasible p v) :
    P12.e.obj (pathologicalParamMapAE p) (pathologicalFwdAE p v) =
      P12.a.obj p v := by
  by_cases hn : p.n = 2
  · let hq : pathParams3 p = pathologicalParamMapAE p := by
      simp [pathologicalParamMapAE, hn]
    rw [show pathologicalFwdAE p v =
        cast (congrArg P12.e.Vars hq) (pathTour3 p) by
      simp [pathologicalFwdAE, hn]]
    rw [pathEObjCast hq, pathTargetObj p _ (pathTour3Feasible p hn),
      pathSourceObj p v h hn]
  · let q : P12.e.Params := { n := p.n, c := p.c, hn := p.hn }
    let w : P12.e.Vars q := { x := v.x, u := v.u }
    let hq : q = pathologicalParamMapAE p := by
      simp [q, pathologicalParamMapAE, hn]
    rw [show pathologicalFwdAE p v = cast (congrArg P12.e.Vars hq) w by
      simp [pathologicalFwdAE, hn, q, w]]
    rw [pathEObjCast hq]
    rfl

private lemma pathologicalBwdObjAE (p : P12.a.Params)
    (v : P12.e.Vars (pathologicalParamMapAE p))
    (h : P12.e.Feasible (pathologicalParamMapAE p) v) :
    P12.e.obj (pathologicalParamMapAE p) v =
      P12.a.obj p (pathologicalBwdAE p v) := by
  by_cases hn : p.n = 2
  · let hq : pathologicalParamMapAE p = pathParams3 p := by
      simp [pathologicalParamMapAE, hn]
    let w : P12.e.Vars (pathParams3 p) := cast (congrArg P12.e.Vars hq) v
    have hw : P12.e.Feasible (pathParams3 p) w := pathEFeasibleCast hq v h
    rw [← pathEObjCast hq v, pathTargetObj p w hw,
      pathSourceObj p _ (pathologicalBwdFeasAE p v h) hn]
  · let q : P12.e.Params := { n := p.n, c := p.c, hn := p.hn }
    let hq : pathologicalParamMapAE p = q := by
      simp [q, pathologicalParamMapAE, hn]
    let w : P12.e.Vars q := cast (congrArg P12.e.Vars hq) v
    rw [← pathEObjCast hq v]
    rw [show pathologicalBwdAE p v = { x := w.x, u := w.u } by
      simp [pathologicalBwdAE, hn, w, q]]
    change P12.e.obj q w = P12.a.obj p { x := w.x, u := w.u }
    rfl

/-- With an unrestricted parameter mapping, the EC1 augmentation is a section
reformulation after all. The only exceptional size is `n = 2`; it is redirected
to a three-city target instance whose costs put the source tour's objective on
every target tour. All larger instances are copied unchanged. -/
noncomputable def aEReformulation :
    MILPReformulation P12.a.formulation P12.e.formulation where
  paramMap := pathologicalParamMapAE
  fwd := pathologicalFwdAE
  bwd := pathologicalBwdAE
  fwd_feas := pathologicalFwdFeasAE
  bwd_feas := pathologicalBwdFeasAE
  bwd_fwd := pathologicalBwdFwdAE
  objMap := id
  objMap_mono := strictMono_id
  fwd_obj := pathologicalFwdObjAE
  bwd_obj := pathologicalBwdObjAE

end P12
