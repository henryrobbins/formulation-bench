import Common
import problems.p7.formulations.a.Formulation
import problems.p7.formulations.b.Formulation
import Mathlib.Data.Sym.Card
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Tactic

open BigOperators Finset

namespace P7

-- ============================================================================
-- § Parameter Mapping
-- ============================================================================

/-- The identity parameter mapping from formulation `a` to formulation `b`.
The two parameter types are structurally identical but distinct. -/
def paramMapAB (p : P7.a.Params) : P7.b.Params :=
  { N := p.N
    hN := p.hN }

-- ============================================================================
-- § Finiteness of the `a`-feasible Set
-- ============================================================================

/-- Encode an assignment by the truth values of each entry. On the feasible set
(where every entry is `0` or `1`) this is injective, so the feasible set embeds
into a finite type. -/
private def encode (p : P7.a.Params) (v : P7.a.Vars p) :
    (Fin p.N → Fin p.N → Bool) × (Fin p.N → P7.a.Strip p.N → Bool) ×
      (Fin p.N → P7.a.Strip p.N → Bool) × (Fin p.N → P7.a.Strip p.N → Bool) :=
  (fun i j => decide (v.h i j = 1),
   fun i ab => decide (v.x i ab = 1),
   fun i ab => decide (v.s i ab = 1),
   fun i ab => decide (v.t i ab = 1))

private lemma feasible_finite (p : P7.a.Params) :
    Set.Finite {v : P7.a.Vars p | P7.a.Feasible p v} := by
  apply Set.Finite.of_finite_image (f := encode p) (Set.toFinite _)
  intro v hv w hw hvw
  simp only [encode, Prod.mk.injEq] at hvw
  obtain ⟨eh, ex, es, et⟩ := hvw
  have hbin : ∀ (f g : ℤ), (f = 0 ∨ f = 1) → (g = 0 ∨ g = 1) →
      (decide (f = 1) = decide (g = 1)) → f = g := by
    intro f g hf hg h
    rw [decide_eq_decide] at h
    rcases hf with h1 | h1 <;> rcases hg with h2 | h2 <;> simp_all
  cases v; cases w
  congr 1
  · funext i j
    exact hbin _ _ (hv.hh_bin i j) (hw.hh_bin i j) (congrFun (congrFun eh i) j)
  · funext i ab
    exact hbin _ _ (hv.hx_bin i ab) (hw.hx_bin i ab) (congrFun (congrFun ex i) ab)
  · funext i ab
    exact hbin _ _ (hv.hs_bin i ab) (hw.hs_bin i ab) (congrFun (congrFun es i) ab)
  · funext i ab
    exact hbin _ _ (hv.ht_bin i ab) (hw.ht_bin i ab) (congrFun (congrFun et i) ab)

-- ============================================================================
-- § Witness Instance
-- ============================================================================

/-- The 3×3 grid instance used as the witness (source side). -/
private abbrev p3 : P7.a.Params := ⟨3, ⟨by decide⟩⟩

/-- The target instance `= paramMapAB p3`, definitionally. -/
private abbrev q3 : P7.b.Params := ⟨p3.N, p3.hN⟩

/-- Repackage a `b`-variable assignment as an `a`-variable assignment. Since `b`
adds only the EC1 cut on top of `a`, this inclusion sends `b`-feasible points to
`a`-feasible points. -/
private def incl (v : P7.b.Vars q3) : P7.a.Vars p3 :=
  { h := v.h, x := v.x, s := v.s, t := v.t }

private lemma incl_maps :
    Set.MapsTo incl {v | P7.b.Feasible q3 v} {v | P7.a.Feasible p3 v} := by
  intro v hv
  exact
    { hrow := hv.hrow, hcol := hv.hcol, hcov := hv.hcov, htop := hv.htop,
      hflow := hv.hflow, hbot := hv.hbot, hh_bin := hv.hh_bin, hx_bin := hv.hx_bin,
      hs_bin := hv.hs_bin, ht_bin := hv.ht_bin }

private lemma incl_inj : Set.InjOn incl {v | P7.b.Feasible q3 v} := by
  intro v _ w _ hvw
  cases v; cases w
  simpa [incl] using hvw

/-- The feasible tiling of the `N = 3` grid depicted in the report. Holes lie at
`(0,1)`, `(1,2)`, `(2,0)`; the tile covering column `0` in rows `0`–`1` extends
past row `0`, so no tile ends immediately left of the hole `(0,1)`. -/
private def wit : P7.a.Vars p3 where
  h := ![![0, 1, 0], ![0, 0, 1], ![1, 0, 0]]
  x i ab := ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 1]],
                ![![1, 0, 0], ![0, 1, 0], ![0, 0, 0]],
                ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]] i ab.val.1 ab.val.2
  s i ab := ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 1]],
                ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]],
                ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]] i ab.val.1 ab.val.2
  t i ab := ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]],
                ![![1, 0, 0], ![0, 1, 0], ![0, 0, 0]],
                ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]] i ab.val.1 ab.val.2

private lemma wit_feasible : P7.a.Feasible p3 wit := by
  refine
    { hrow := ?_, hcol := ?_, hcov := ?_, htop := ?_, hflow := ?_, hbot := ?_,
      hh_bin := ?_, hx_bin := ?_, hs_bin := ?_, ht_bin := ?_ } <;> decide

/-- `wit` violates the EC1 cut at the hole `(0,1)`, so it is not `b`-feasible;
hence it lies outside the image of the inclusion of `b`-feasible points. -/
private lemma wit_missing : wit ∉ incl '' {v | P7.b.Feasible q3 v} := by
  rintro ⟨v, hv, hgv⟩
  simp only [incl, wit, P7.a.Vars.mk.injEq] at hgv
  obtain ⟨hh, _, _, ht⟩ := hgv
  have hcut := hv.hec1 0 1 (by decide)
  rw [hh, ht] at hcut
  revert hcut
  decide

-- ============================================================================
-- § Disproof
-- ============================================================================

/-- Formulation `b` (IMO6 augmented with the invalid EC1 cut of EvoCut v1) is
**not** a reformulation of formulation `a` (IMO6) under the identity parameter
mapping: no `MILPReformulation` whose `paramMap` is `paramMapAB` can exist.

Unlike the TSP cuts, EC1 does not empty the feasible set — it merely removes some
feasible tilings. Witness: the `N = 3` tiling `wit` is `a`-feasible but violates
EC1 at the hole `(0,1)` (the tile immediately left of the hole continues below,
so it does not end there). Thus `b`'s feasible set is a *proper* subset of `a`'s.
`MILPReformulation.false_of_feasible_embeds_missing` turns this into a
contradiction: `Φ.fwd` injects `a`-feasibles into `b`-feasibles, the inclusion
injects `b`-feasibles back missing `wit`, forcing `|F_a| ≤ |F_b| < |F_a|`. -/
theorem not_aBReformulation
    (Φ : MILPReformulation P7.a.formulation P7.b.formulation)
    (hΦ : Φ.paramMap = paramMapAB) : False := by
  obtain ⟨pm, fwd, bwd, fwd_feas, bwd_feas, bwd_fwd, om, om_mono, fwd_obj, bwd_obj⟩ := Φ
  subst hΦ
  exact MILPReformulation.false_of_feasible_embeds_missing
    (F := P7.a.formulation) (G := P7.b.formulation)
    ⟨paramMapAB, fwd, bwd, fwd_feas, bwd_feas, bwd_fwd, om, om_mono, fwd_obj, bwd_obj⟩
    p3 (feasible_finite p3) incl incl_maps incl_inj wit wit_feasible wit_missing

-- ============================================================================
-- § Unconditional Disproof
-- ============================================================================

/-- The integer-valued objective before its coercion to `ℝ`. -/
private def aStartCount (p : P7.a.Params) (v : P7.a.Vars p) : ℤ :=
  ∑ i : Fin p.N, ∑ ab : P7.a.Strip p.N, v.s i ab

private lemma a_obj_eq_startCount (p : P7.a.Params) (v : P7.a.Vars p) :
    P7.a.obj p v = (aStartCount p v : ℝ) := by
  simp only [P7.a.obj, aStartCount, Int.cast_sum]

/-- Forget the EC1 constraint and repackage a target assignment as a source
assignment of the same grid size. -/
private def forgetEC1Params (q : P7.b.Params) : P7.a.Params :=
  { N := q.N, hN := q.hN }

private def forgetEC1 (q : P7.b.Params) (v : P7.b.Vars q) :
    P7.a.Vars (forgetEC1Params q) :=
  { h := v.h, x := v.x, s := v.s, t := v.t }

private lemma forgetEC1_feasible (q : P7.b.Params) (v : P7.b.Vars q)
    (h : P7.b.Feasible q v) :
    P7.a.Feasible (forgetEC1Params q) (forgetEC1 q v) :=
  { hrow := h.hrow, hcol := h.hcol, hcov := h.hcov, htop := h.htop,
    hflow := h.hflow, hbot := h.hbot, hh_bin := h.hh_bin, hx_bin := h.hx_bin,
    hs_bin := h.hs_bin, ht_bin := h.ht_bin }

private lemma forgetEC1_obj (q : P7.b.Params) (v : P7.b.Vars q) :
    P7.a.obj (forgetEC1Params q) (forgetEC1 q v) = P7.b.obj q v := by
  rfl

/-- Independent off-diagonal zero-flow toggles.  The first coordinate is a
non-top row; a member `(i,(a,b))` switches on `s i a b` and `t (i-1) a b`. -/
private def toggleSlots (N : ℕ) :
    Finset (Fin N × P7.b.Strip N) :=
  univ.filter (fun slot => 0 < slot.1.val ∧ slot.2.val.1 ≠ slot.2.val.2)

private lemma toggleSlots_card (N : ℕ) (hN : 0 < N) :
    (toggleSlots N).card = (N - 1) * N.choose 2 := by
  let z : Fin N := ⟨0, hN⟩
  have hpos : univ.filter (fun i : Fin N => 0 < i.val) = univ.erase z := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_erase]
    constructor
    · intro hi
      refine ⟨?_, trivial⟩
      intro hiz
      have hv := congrArg Fin.val hiz
      simp [z] at hv
      omega
    · rintro ⟨hiz, _⟩
      by_contra hnotpos
      apply hiz
      apply Fin.ext
      simp [z]
      omega
  have hstrict :
      (univ.filter (fun ab : P7.b.Strip N => ab.val.1 ≠ ab.val.2)).card = N.choose 2 := by
    rw [← Fintype.card_subtype]
    calc
      Fintype.card {ab : P7.b.Strip N // ab.val.1 ≠ ab.val.2} =
          Fintype.card {s : Sym2 (Fin N) // ¬s.IsDiag} := Fintype.card_congr <|
        (Sym2.sortEquiv.symm).subtypeEquiv (fun ab => by
          change ab.val.1 ≠ ab.val.2 ↔ ¬Sym2.IsDiag (Sym2.mk ab.val)
          rw [Sym2.isDiag_iff_proj_eq])
      _ = (Fintype.card (Fin N)).choose 2 := Sym2.card_subtype_not_diag
      _ = N.choose 2 := by rw [Fintype.card_fin]
  have hprod : toggleSlots N =
      (univ.filter (fun i : Fin N => 0 < i.val)) ×ˢ
        (univ.filter (fun ab : P7.b.Strip N => ab.val.1 ≠ ab.val.2)) := by
    ext slot
    simp [toggleSlots]
  rw [hprod, card_product, hpos, card_erase_of_mem (mem_univ z), hstrict]
  simp only [card_univ, Fintype.card_fin]

private def toggleVars (q : P7.b.Params)
    (S : Finset (Fin q.N × P7.b.Strip q.N)) : P7.b.Vars q where
  h i j := if i = j then 1 else 0
  x i ab := if ab.val.1 = ab.val.2 ∧ i ≠ ab.val.1 then 1 else 0
  s i ab :=
    if ab.val.1 = ab.val.2 then (if i ≠ ab.val.1 then 1 else 0)
    else if (i, ab) ∈ S then 1 else 0
  t i ab :=
    if ab.val.1 = ab.val.2 then (if i ≠ ab.val.1 then 1 else 0)
    else if ∃ k : Fin q.N, k.val = i.val + 1 ∧ (k, ab) ∈ S then 1 else 0

private lemma toggleVars_feasible (q : P7.b.Params)
    (S : Finset (Fin q.N × P7.b.Strip q.N))
    (hS : S ⊆ toggleSlots q.N) :
    P7.b.Feasible q (toggleVars q S) := by
  let _ := q.hN
  refine
    { hrow := ?_, hcol := ?_, hcov := ?_, htop := ?_, hflow := ?_, hbot := ?_,
      hh_bin := ?_, hx_bin := ?_, hs_bin := ?_, ht_bin := ?_, hec1 := ?_ }
  · intro i
    simp [toggleVars]
  · intro j
    simp [toggleVars]
  · intro i j
    classical
    let jj : P7.b.Strip q.N := ⟨(j, j), by simp⟩
    rw [Finset.sum_eq_single jj]
    · by_cases hij : i = j <;> simp [toggleVars, hij, jj]
    · intro ab habmem habne
      have hnotdiag : ab.val.1 ≠ ab.val.2 := by
        intro heq
        have hc : ab.val.1.val ≤ j.val ∧ j.val ≤ ab.val.2.val := by
          simpa [P7.b.strips_covering] using habmem
        have hev : ab.val.1.val = ab.val.2.val := congrArg Fin.val heq
        have hleft : ab.val.1 = j := Fin.ext (by omega)
        have hright : ab.val.2 = j := Fin.ext (by omega)
        have hab_eq : ab = ⟨(j, j), by simp⟩ := Subtype.ext (Prod.ext hleft hright)
        exact habne hab_eq
      simp [toggleVars, hnotdiag]
    · intro hnotmem
      exfalso
      apply hnotmem
      simp [P7.b.strips_covering, jj]
  · intro ab
    by_cases hab : ab.val.1 = ab.val.2
    · simp [toggleVars, hab]
    · have hnmem : ((0 : Fin q.N), ab) ∉ S := by
        intro hm
        have hslt := hS hm
        simp [toggleSlots] at hslt
      simp [toggleVars, hab, hnmem]
  · intro i ab hi
    by_cases hab : ab.val.1 = ab.val.2
    · simp [toggleVars, hab]
    · have hprev : (i.val - 1) + 1 = i.val := by omega
      have hex :
          (∃ k : Fin q.N, k.val = (i.val - 1) + 1 ∧ (k, ab) ∈ S) ↔
            (i, ab) ∈ S := by
        constructor
        · rintro ⟨k, hk, hmem⟩
          have hki : k = i := Fin.ext (by omega)
          simpa [hki] using hmem
        · intro hmem
          exact ⟨i, hprev.symm, hmem⟩
      simp [toggleVars, hab, hex]
  · intro ab
    by_cases hab : ab.val.1 = ab.val.2
    · simp [toggleVars, hab]
    · have hnex : ¬ ∃ k : Fin q.N,
          k.val = (q.N - 1) + 1 ∧ (k, ab) ∈ S := by
        rintro ⟨k, hk, _⟩
        have hklt := k.isLt
        omega
      simp [toggleVars, hab, hnex]
  · intro i j
    simp only [toggleVars]
    split_ifs <;> simp_all
  · intro i ab
    simp only [toggleVars]
    split_ifs <;> simp_all
  · intro i ab
    simp only [toggleVars]
    split_ifs <;> simp_all
  · intro i ab
    simp only [toggleVars]
    split_ifs <;> simp_all
  · intro i j hj
    classical
    have ht_nonneg : ∀ ab : P7.b.Strip q.N,
        0 ≤ (toggleVars q S).t i ab := by
      intro ab
      simp only [toggleVars]
      split_ifs <;> omega
    by_cases hij : i = j
    · subst i
      let a : Fin q.N := ⟨j.val - 1, by omega⟩
      have hja : j ≠ a := by
        apply Fin.ne_of_val_ne
        simp [a]
        omega
      let aa : P7.b.Strip q.N := ⟨(a, a), by simp⟩
      have haa_mem : aa ∈ P7.b.strips_ending_before q.N j := by
        simp [P7.b.strips_ending_before, a, aa]
      have hsingle :
          (toggleVars q S).t j aa ≤
            ∑ ab ∈ P7.b.strips_ending_before q.N j,
              (toggleVars q S).t j ab :=
        Finset.single_le_sum
          (f := fun ab : P7.b.Strip q.N => (toggleVars q S).t j ab)
          (fun ab _ => ht_nonneg ab) haa_mem
      simpa [toggleVars, aa, hja] using hsingle
    · have hsum_nonneg :
          0 ≤ ∑ ab ∈ P7.b.strips_ending_before q.N j,
            (toggleVars q S).t i ab := by
        exact Finset.sum_nonneg (fun ab _ => ht_nonneg ab)
      simpa [toggleVars, hij] using hsum_nonneg

private lemma toggleVars_obj (q : P7.b.Params)
    (S : Finset (Fin q.N × P7.b.Strip q.N))
    (hS : S ⊆ toggleSlots q.N) :
    P7.b.obj q (toggleVars q S) = (q.N * (q.N - 1) + S.card : ℕ) := by
  simp only [P7.b.obj, toggleVars]
  norm_cast
  have hSoff : ∀ z ∈ S, z.2.val.1 ≠ z.2.val.2 := by
    intro z hz
    have hs : 0 < z.1.val ∧ z.2.val.1 ≠ z.2.val.2 := by
      simpa only [toggleSlots, mem_filter, mem_univ, true_and] using hS hz
    exact hs.2
  have hpoint : ∀ (i : Fin q.N) (ab : P7.b.Strip q.N),
      (if ab.val.1 = ab.val.2 then (if i ≠ ab.val.1 then (1 : ℕ) else 0)
        else if (i, ab) ∈ S then 1 else 0) =
      (if ab.val.1 = ab.val.2 ∧ i ≠ ab.val.1 then 1 else 0) +
        (if (i, ab) ∈ S then 1 else 0) := by
    intro i ab
    by_cases hab : ab.val.1 = ab.val.2
    · have hnmem : (i, ab) ∉ S := by
        intro hm
        exact hSoff (i, ab) hm hab
      simp [hab, hnmem]
    · simp [hab]
  have hdiag_one (i : Fin q.N) :
      (∑ ab : P7.b.Strip q.N,
        if ab.val.1 = ab.val.2 ∧ i ≠ ab.val.1 then 1 else 0) = q.N - 1 := by
    rw [Finset.sum_boole]
    let diag : Fin q.N → P7.b.Strip q.N := fun a => ⟨(a, a), by simp⟩
    have hdiag :
        univ.filter (fun ab : P7.b.Strip q.N => ab.val.1 = ab.val.2 ∧ i ≠ ab.val.1) =
          (univ.erase i).map ⟨diag, fun a b h => by
            apply Fin.ext
            have hv := congrArg (fun ab : P7.b.Strip q.N => ab.val.1.val) h
            simpa only [diag] using hv⟩ := by
      ext ab
      simp only [mem_filter, mem_univ, true_and, mem_map, mem_erase]
      constructor
      · rintro ⟨hab, hi⟩
        refine ⟨ab.val.1, ⟨ne_comm.mp hi, trivial⟩, ?_⟩
        apply Subtype.ext
        exact Prod.ext rfl hab
      · rintro ⟨a, hia, rfl⟩
        exact ⟨rfl, ne_comm.mpr hia.1⟩
    rw [hdiag, card_map]
    simp
  have hSsum :
      (∑ i : Fin q.N, ∑ ab : P7.b.Strip q.N,
        if (i, ab) ∈ S then 1 else 0) = S.card := by
    calc
      (∑ i : Fin q.N, ∑ ab : P7.b.Strip q.N,
          if (i, ab) ∈ S then 1 else 0) =
          ∑ z ∈ (univ : Finset (Fin q.N)) ×ˢ
              (univ : Finset (P7.b.Strip q.N)),
            if z ∈ S then 1 else 0 := by
              symm
              exact Finset.sum_product _ _ _
      _ = S.card := by
        rw [Finset.sum_boole]
        simp
  calc
    (∑ i, ∑ ab, if ab.val.1 = ab.val.2 then (if i ≠ ab.val.1 then (1 : ℕ) else 0)
        else if (i, ab) ∈ S then 1 else 0)
        = ∑ i, ∑ ab,
            ((if ab.val.1 = ab.val.2 ∧ i ≠ ab.val.1 then 1 else 0) +
              (if (i, ab) ∈ S then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro ab _
          exact hpoint i ab
    _ = q.N * (q.N - 1) + S.card := by
      simp_rw [Finset.sum_add_distrib, hdiag_one]
      rw [hSsum]
      simp

private def lowerBand (N : ℕ) : Set ℝ :=
  (fun k : ℤ => (k : ℝ)) ''
    (↑(Finset.Icc ((N * (N - 1) : ℕ) : ℤ)
      ((N * (N - 1) + (N - 1) * N.choose 2 : ℕ) : ℤ)) : Set ℤ)

private lemma lowerBand_subset_values (q : P7.b.Params) :
    lowerBand q.N ⊆ P7.b.formulation.values q := by
  rintro value ⟨k, hk, rfl⟩
  simp only [Finset.mem_coe, Finset.mem_Icc] at hk
  let base : ℕ := q.N * (q.N - 1)
  let width : ℕ := (q.N - 1) * q.N.choose 2
  let d : ℕ := (k - (base : ℤ)).toNat
  have hd_nonneg : 0 ≤ k - (base : ℤ) := by
    dsimp [base]
    omega
  have hd_cast : (d : ℤ) = k - (base : ℤ) := by
    exact Int.toNat_of_nonneg hd_nonneg
  have hd_le : d ≤ width := by
    dsimp [width, base] at hd_cast ⊢
    omega
  have hd_slots : d ≤ (toggleSlots q.N).card := by
    rw [toggleSlots_card q.N (Nat.pos_of_ne_zero q.hN.out)]
    exact hd_le
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq hd_slots
  refine ⟨toggleVars q S, toggleVars_feasible q S hS, ?_⟩
  change P7.b.obj q (toggleVars q S) = (k : ℝ)
  rw [toggleVars_obj q S hS, hScard]
  norm_cast
  dsimp [d, base] at hd_cast ⊢
  omega

private lemma lowerBand_subset_a_values (p : P7.a.Params) :
    lowerBand p.N ⊆ P7.a.formulation.values p := by
  intro value hvalue
  rcases lowerBand_subset_values (paramMapAB p) hvalue with ⟨v, hv, hobj⟩
  exact
    ⟨forgetEC1 (paramMapAB p) v, forgetEC1_feasible (paramMapAB p) v hv,
      (forgetEC1_obj (paramMapAB p) v).trans hobj⟩

private lemma lowerBand_ncard (N : ℕ) :
    (lowerBand N).ncard = (N - 1) * N.choose 2 + 1 := by
  rw [lowerBand, Set.ncard_image_of_injective _ Int.cast_injective,
    Set.ncard_coe_finset, Int.card_Icc]
  have h :
      ((N * (N - 1) + (N - 1) * N.choose 2 : ℕ) : ℤ) + 1 -
          ((N * (N - 1) : ℕ) : ℤ) =
        (((N - 1) * N.choose 2 + 1 : ℕ) : ℤ) := by
    push_cast
    omega
  rw [h, Int.toNat_natCast]

private def upperBand (N : ℕ) : Set ℝ :=
  (fun k : ℤ => (k : ℝ)) ''
    (↑(Finset.Icc 0 ((N * (N + 1).choose 2 : ℕ) : ℤ)) : Set ℤ)

private lemma strip_card (N : ℕ) :
    Fintype.card (P7.a.Strip N) = (N + 1).choose 2 := by
  calc
    _ = Fintype.card (Sym2 (Fin N)) :=
      Fintype.card_congr Sym2.sortEquiv.symm
    _ = (Fintype.card (Fin N) + 1).choose 2 := Sym2.card
    _ = (N + 1).choose 2 := by rw [Fintype.card_fin]

private lemma a_values_subset_upperBand (p : P7.a.Params) :
    P7.a.formulation.values p ⊆ upperBand p.N := by
  rintro value ⟨v, hv, rfl⟩
  refine ⟨aStartCount p v, ?_, (a_obj_eq_startCount p v).symm⟩
  simp only [Finset.mem_coe, Finset.mem_Icc]
  constructor
  · exact sum_nonneg fun i _ => sum_nonneg fun ab _ => by
      rcases hv.hs_bin i ab with h | h <;> omega
  · calc
      aStartCount p v ≤
          ∑ _i : Fin p.N, ∑ _ab : P7.a.Strip p.N, (1 : ℤ) := by
        apply sum_le_sum
        intro i _
        apply sum_le_sum
        intro ab _
        rcases hv.hs_bin i ab with h | h <;> omega
      _ = (p.N * (p.N + 1).choose 2 : ℕ) := by
        simp [strip_card]

private lemma b_values_subset_upperBand (q : P7.b.Params) :
    P7.b.formulation.values q ⊆ upperBand q.N := by
  rintro value ⟨v, hv, rfl⟩
  have ha := a_values_subset_upperBand (forgetEC1Params q)
    ⟨forgetEC1 q v, forgetEC1_feasible q v hv, rfl⟩
  simpa only [forgetEC1Params, forgetEC1_obj] using ha

private lemma upperBand_ncard (N : ℕ) :
    (upperBand N).ncard = N * (N + 1).choose 2 + 1 := by
  rw [upperBand, Set.ncard_image_of_injective _ Int.cast_injective,
    Set.ncard_coe_finset, Int.card_Icc]
  change ((((N * (N + 1).choose 2 : ℕ) : ℤ) + 1).toNat =
    N * (N + 1).choose 2 + 1)
  rw [show ((N * (N + 1).choose 2 : ℕ) : ℤ) + 1 =
      ((N * (N + 1).choose 2 + 1 : ℕ) : ℤ) by norm_num,
    Int.toNat_natCast]

private lemma upperBand_finite (N : ℕ) : (upperBand N).Finite := by
  exact (Finset.finite_toSet _).image _

private lemma a_obj_pos (p : P7.a.Params) (v : P7.a.Vars p)
    (hv : P7.a.Feasible p v) (hN : 1 < p.N) : 0 < P7.a.obj p v := by
  let _ := p.hN
  have hj : ∃ j : Fin p.N, v.h 0 j = 0 := by
    by_contra h
    push_neg at h
    have hall : ∀ j : Fin p.N, v.h 0 j = 1 := by
      intro j
      exact (hv.hh_bin 0 j).resolve_left (h j)
    have hr := hv.hrow 0
    simp_rw [hall] at hr
    simp at hr
    omega
  obtain ⟨j, hj⟩ := hj
  have hsum : ∑ ab ∈ P7.a.strips_covering p.N j, v.x 0 ab = 1 := by
    have := hv.hcov 0 j
    omega
  have hex : ∃ ab ∈ P7.a.strips_covering p.N j, v.x 0 ab ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : ∑ ab ∈ P7.a.strips_covering p.N j, v.x 0 ab = 0 := by
      exact sum_eq_zero fun ab hab => h ab hab
    omega
  obtain ⟨ab, habmem, hab⟩ := hex
  have hx : v.x 0 ab = 1 := (hv.hx_bin 0 ab).resolve_left hab
  have hs : v.s 0 ab = 1 := by
    rw [← hv.htop ab]
    exact hx
  have hs_nonneg : ∀ i : Fin p.N, ∀ cd : P7.a.Strip p.N, 0 ≤ v.s i cd := by
    intro i cd
    rcases hv.hs_bin i cd with h | h <;> omega
  have hab_le : v.s 0 ab ≤ ∑ cd : P7.a.Strip p.N, v.s 0 cd :=
    Finset.single_le_sum (fun cd _ => hs_nonneg 0 cd) (mem_univ ab)
  have hrow_le : (∑ cd : P7.a.Strip p.N, v.s 0 cd) ≤ aStartCount p v :=
    Finset.single_le_sum
      (fun i _ => sum_nonneg fun cd _ => hs_nonneg i cd) (mem_univ (0 : Fin p.N))
  rw [a_obj_eq_startCount]
  exact_mod_cast hs.symm.le.trans (hab_le.trans hrow_le)

private lemma source_values_card_upper_strict (p : P7.a.Params) (hN : 1 < p.N) :
    (P7.a.formulation.values p).ncard ≤ p.N * (p.N + 1).choose 2 := by
  let s := upperBand p.N \ {0}
  have hsub : P7.a.formulation.values p ⊆ s := by
    rintro value hv
    refine ⟨a_values_subset_upperBand p hv, ?_⟩
    rintro rfl
    obtain ⟨v, hfeas, hobj⟩ := hv
    change P7.a.obj p v = 0 at hobj
    have := a_obj_pos p v hfeas hN
    linarith
  have hzero : (0 : ℝ) ∈ upperBand p.N := by
    refine ⟨0, ?_, by norm_num⟩
    simp only [Finset.mem_coe, Finset.mem_Icc]
    constructor <;> positivity
  calc
    (P7.a.formulation.values p).ncard ≤ s.ncard :=
      Set.ncard_le_ncard hsub (upperBand_finite p.N).diff
    _ = (upperBand p.N).ncard - 1 := Set.ncard_diff_singleton_of_mem hzero
    _ = p.N * (p.N + 1).choose 2 := by rw [upperBand_ncard]; omega

private lemma target_values_card_upper_strict (q : P7.b.Params) (hN : 1 < q.N) :
    (P7.b.formulation.values q).ncard ≤ q.N * (q.N + 1).choose 2 := by
  have hsub : P7.b.formulation.values q ⊆
      P7.a.formulation.values (forgetEC1Params q) := by
    rintro value ⟨v, hv, hobj⟩
    exact ⟨forgetEC1 q v, forgetEC1_feasible q v hv,
      (forgetEC1_obj q v).trans hobj⟩
  exact (Set.ncard_le_ncard hsub
    ((upperBand_finite q.N).subset (a_values_subset_upperBand (forgetEC1Params q)))).trans
      (source_values_card_upper_strict (forgetEC1Params q) hN)

private lemma source_values_card_one (p : P7.a.Params) (hN : p.N = 1) :
    (P7.a.formulation.values p).ncard ≤ 1 := by
  rcases p with ⟨N, hne⟩
  simp only at hN
  subst N
  let p : P7.a.Params := ⟨1, hne⟩
  let _ := p.hN
  have hsub : P7.a.formulation.values p ⊆ ({0} : Set ℝ) := by
    rintro value ⟨v, hv, rfl⟩
    have hh := hv.hrow (0 : Fin p.N)
    have hc := hv.hcov (0 : Fin p.N) (0 : Fin p.N)
    have ht := hv.htop
      (⟨((0 : Fin p.N), (0 : Fin p.N)), by simp⟩ : P7.a.Strip p.N)
    simp only [Set.mem_singleton_iff]
    simp [P7.a.strips_covering, p] at hc
    let strip0 : P7.a.Strip 1 := ⟨(0, 0), by simp⟩
    letI : Unique (P7.a.Strip 1) :=
      { default := strip0
        uniq := fun ab => by
          apply Subtype.ext
          exact Prod.ext (Fin.eq_zero _) (Fin.eq_zero _) }
    change (∑ i : Fin 1, ∑ ab : P7.a.Strip 1, (v.s i ab : ℝ)) = 0
    rw [Fin.sum_univ_one, Fintype.sum_unique]
    have hstrip : (default : P7.a.Strip 1) = strip0 := rfl
    rw [hstrip]
    have ht0 : v.x 0 strip0 = v.s 0 strip0 := by simpa [p, strip0] using ht
    have hh0 : v.h 0 0 = 1 := by simpa [p] using hh
    rw [Fintype.sum_unique] at hc
    have hc' : v.x 0 (default : P7.a.Strip 1) = 0 := by omega
    have hc0 : v.x 0 strip0 = 0 := by simpa [strip0] using hc'
    rw [← ht0, hc0]
    norm_num
  simpa [p] using Set.ncard_le_ncard hsub (Set.finite_singleton 0)

private lemma target_values_card_one (q : P7.b.Params) (hN : q.N = 1) :
    (P7.b.formulation.values q).ncard ≤ 1 := by
  have hsub : P7.b.formulation.values q ⊆
      P7.a.formulation.values (forgetEC1Params q) := by
    rintro value ⟨v, hv, hobj⟩
    exact ⟨forgetEC1 q v, forgetEC1_feasible q v hv,
      (forgetEC1_obj q v).trans hobj⟩
  exact (Set.ncard_le_ncard hsub
    ((upperBand_finite q.N).subset (a_values_subset_upperBand (forgetEC1Params q)))).trans
      (source_values_card_one (forgetEC1Params q) hN)

private lemma source_values_card_upper (p : P7.a.Params) :
    (P7.a.formulation.values p).ncard ≤ p.N * (p.N + 1).choose 2 + 1 := by
  rw [← upperBand_ncard]
  exact Set.ncard_le_ncard (a_values_subset_upperBand p) (upperBand_finite p.N)

private lemma target_values_card_lower (q : P7.b.Params) :
    (q.N - 1) * q.N.choose 2 + 1 ≤ (P7.b.formulation.values q).ncard := by
  rw [← lowerBand_ncard]
  exact Set.ncard_le_ncard (lowerBand_subset_values q)
    ((upperBand_finite q.N).subset (b_values_subset_upperBand q))

private lemma source_values_card_lower (p : P7.a.Params) :
    (p.N - 1) * p.N.choose 2 + 1 ≤ (P7.a.formulation.values p).ncard := by
  rw [← lowerBand_ncard]
  exact Set.ncard_le_ncard (lowerBand_subset_a_values p)
    ((upperBand_finite p.N).subset (a_values_subset_upperBand p))

private lemma target_values_card_upper (q : P7.b.Params) :
    (P7.b.formulation.values q).ncard ≤ q.N * (q.N + 1).choose 2 + 1 := by
  rw [← upperBand_ncard]
  exact Set.ncard_le_ncard (b_values_subset_upperBand q) (upperBand_finite q.N)

private lemma value_card_bands_disjoint {N M : ℕ} (hNM : N < M) :
    N * (N + 1).choose 2 ≤ (M - 1) * M.choose 2 := by
  have hsub : N ≤ M - 1 := by omega
  have hchoose : (N + 1).choose 2 ≤ M.choose 2 :=
    Nat.choose_le_choose 2 (by omega)
  calc
    N * (N + 1).choose 2 ≤ N * M.choose 2 := Nat.mul_le_mul_left N hchoose
    _ ≤ (M - 1) * M.choose 2 := Nat.mul_le_mul_right _ hsub

/-- Any section reformulation from `a` to the EC1 augmentation must preserve
the grid size.  For `N > 1`, positivity and binary starts bound the source by
`N * choose (N + 1) 2` objective values.  At any larger size `M`, independent
zero-flow toggles on the valid strict strips give
`(M - 1) * choose M 2 + 1` target values, which is strictly larger.  The
singleton `N = 1` objective-value set is handled separately. -/
private lemma paramMap_eq_of_reformulation
    (Φ : MILPReformulation P7.a.formulation P7.b.formulation) :
    Φ.paramMap = paramMapAB := by
  funext p
  let q := Φ.paramMap p
  have hbij := Φ.objMap_bijOn p
  have hcard :
      (P7.a.formulation.values p).ncard =
        (P7.b.formulation.values q).ncard :=
    Set.ncard_congr (fun v _ => Φ.objMap v) hbij.mapsTo
      (fun _ _ hv hw h => hbij.injOn hv hw h)
      (fun v hv => by
        obtain ⟨w, hw, rfl⟩ := hbij.surjOn hv
        exact ⟨w, hw, rfl⟩)
  have hp_pos : 0 < p.N := Nat.pos_of_ne_zero p.hN.out
  have hq_pos : 0 < q.N := Nat.pos_of_ne_zero q.hN.out
  have hN : p.N = q.N := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hpq | hqp
    · have hlower := target_values_card_lower q
      rw [← hcard] at hlower
      by_cases hp1 : p.N = 1
      · have hupper := source_values_card_one p hp1
        have hq2 : 2 ≤ q.N := by omega
        have hwidth : 1 ≤ (q.N - 1) * q.N.choose 2 := by
          exact Nat.mul_pos (by omega) (Nat.choose_pos hq2)
        omega
      · have hp2 : 1 < p.N := by omega
        have hupper := source_values_card_upper_strict p hp2
        have hband := value_card_bands_disjoint hpq
        omega
    · have hlower := source_values_card_lower p
      rw [hcard] at hlower
      by_cases hq1 : q.N = 1
      · have hupper := target_values_card_one q hq1
        have hp2 : 2 ≤ p.N := by omega
        have hwidth : 1 ≤ (p.N - 1) * p.N.choose 2 := by
          exact Nat.mul_pos (by omega) (Nat.choose_pos hp2)
        omega
      · have hq2 : 1 < q.N := by omega
        have hupper := target_values_card_upper_strict q hq2
        have hband := value_card_bands_disjoint hqp
        omega
  have hqeq : q = paramMapAB p := by
    cases hq : q with
    | mk N h =>
      have hN' : p.N = N := by simpa only [hq] using hN
      cases p with
      | mk M hp =>
        simp only [paramMapAB] at hN' ⊢
        subst N
        rfl
  exact hqeq

/-- Formulation `b` (IMO6 augmented with the invalid EC1 cut) is not a
reformulation of formulation `a` under any parameter map. Objective-value-set
cardinality first forces the parameter map to be `paramMapAB`, after which
`not_aBReformulation` supplies the existing `N = 3` feasible-set
contradiction. -/
theorem not_aBReformulation_any_paramMap
    (Φ : MILPReformulation P7.a.formulation P7.b.formulation) : False :=
  not_aBReformulation Φ (paramMap_eq_of_reformulation Φ)

end P7
