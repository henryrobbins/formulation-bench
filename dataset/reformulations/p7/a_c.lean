import Common
import problems.p7.formulations.a.Formulation
import problems.p7.formulations.c.Formulation
import Mathlib.Tactic

open BigOperators Finset

namespace P7

-- ============================================================================
-- § Parameter Mapping
-- ============================================================================

/-- The identity parameter mapping from formulation `a` to formulation `c`.
The two parameter types are structurally identical but distinct. -/
def paramMapAC (p : P7.a.Params) : P7.c.Params :=
  { N := p.N
    hN := p.hN }

-- ============================================================================
-- § Finiteness of the `a`-feasible Set
-- ============================================================================

/-- Encode an assignment by the truth values of each entry. On the feasible set
(where every entry is `0` or `1`) this is injective, so the feasible set embeds
into a finite type. -/
private def encode (p : P7.a.Params) (v : P7.a.Vars p) :
    (Fin p.N → Fin p.N → Bool) × (Fin p.N → Fin p.N → Fin p.N → Bool) ×
      (Fin p.N → Fin p.N → Fin p.N → Bool) × (Fin p.N → Fin p.N → Fin p.N → Bool) :=
  (fun i j => decide (v.h i j = 1),
   fun i a b => decide (v.x i a b = 1),
   fun i a b => decide (v.s i a b = 1),
   fun i a b => decide (v.t i a b = 1))

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
  · funext i a b
    exact hbin _ _ (hv.hx_bin i (a, b)) (hw.hx_bin i (a, b)) (congrFun (congrFun (congrFun ex i) a) b)
  · funext i a b
    exact hbin _ _ (hv.hs_bin i (a, b)) (hw.hs_bin i (a, b)) (congrFun (congrFun (congrFun es i) a) b)
  · funext i a b
    exact hbin _ _ (hv.ht_bin i (a, b)) (hw.ht_bin i (a, b)) (congrFun (congrFun (congrFun et i) a) b)

-- ============================================================================
-- § Witness Instance
-- ============================================================================

/-- The degenerate 3-city instance used as the witness (source side). -/
private abbrev p3 : P7.a.Params := ⟨3, ⟨by decide⟩⟩

/-- The target instance `= paramMapAC p3`, definitionally. -/
private abbrev q3 : P7.c.Params := ⟨p3.N, p3.hN⟩

/-- Repackage a `c`-variable assignment as an `a`-variable assignment. Since `c`
adds only the EC2 cut on top of `a`, this inclusion sends `c`-feasible points to
`a`-feasible points. -/
private def incl (v : P7.c.Vars q3) : P7.a.Vars p3 :=
  { h := v.h, x := v.x, s := v.s, t := v.t }

private lemma incl_maps :
    Set.MapsTo incl {v | P7.c.Feasible q3 v} {v | P7.a.Feasible p3 v} := by
  intro v hv
  exact
    { hrow := hv.hrow, hcol := hv.hcol, hcov := hv.hcov, htop := hv.htop,
      hflow := hv.hflow, hbot := hv.hbot, hh_bin := hv.hh_bin, hx_bin := hv.hx_bin,
      hs_bin := hv.hs_bin, ht_bin := hv.ht_bin }

private lemma incl_inj : Set.InjOn incl {v | P7.c.Feasible q3 v} := by
  intro v _ w _ hvw
  cases v; cases w
  simpa [incl] using hvw

/-- A feasible tiling of the `N = 3` grid with holes at `(0,2)`, `(1,0)`,
`(2,1)`. The tile covering column `2` in rows `1`–`2` starts above row `2`, so no
tile starts immediately right of the hole `(1,0)`. -/
private def wit : P7.a.Vars p3 where
  h := ![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]]
  x := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 0]],
         ![![0, 0, 0], ![0, 1, 0], ![0, 0, 1]],
         ![![1, 0, 0], ![0, 0, 0], ![0, 0, 1]]]
  s := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 0]],
         ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]],
         ![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]]]
  t := ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]],
         ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]],
         ![![1, 0, 0], ![0, 0, 0], ![0, 0, 1]]]

private lemma wit_feasible : P7.a.Feasible p3 wit := by
  refine
    { hrow := ?_, hcol := ?_, hcov := ?_, htop := ?_, hflow := ?_, hbot := ?_,
      hh_bin := ?_, hx_bin := ?_, hs_bin := ?_, ht_bin := ?_ } <;> decide

/-- `wit` violates the EC2 cut at the hole `(1,0)`, so it is not `c`-feasible;
hence it lies outside the image of the inclusion of `c`-feasible points. -/
private lemma wit_missing : wit ∉ incl '' {v | P7.c.Feasible q3 v} := by
  rintro ⟨v, hv, hgv⟩
  simp only [incl, wit, P7.a.Vars.mk.injEq] at hgv
  obtain ⟨hh, _, hs, _⟩ := hgv
  have hcut := hv.hec2 1 0 (by decide)
  rw [hh, hs] at hcut
  revert hcut
  decide

-- ============================================================================
-- § Disproof
-- ============================================================================

/-- Formulation `c` (IMO6 augmented with the invalid EC2 cut of EvoCut v1) is
**not** a reformulation of formulation `a` (IMO6) under the identity parameter
mapping: no `MILPReformulation` whose `paramMap` is `paramMapAC` can exist.

Unlike the TSP cuts, EC2 does not empty the feasible set — it merely removes some
feasible tilings. Witness: the `N = 3` tiling `wit` is `a`-feasible but violates
EC2 at the hole `(1,0)` (the tile immediately right of the hole starts above, so
it does not start there). Thus `c`'s feasible set is a *proper* subset of `a`'s.
`MILPReformulation.false_of_feasible_embeds_missing` turns this into a
contradiction: `Φ.fwd` injects `a`-feasibles into `c`-feasibles, the inclusion
injects `c`-feasibles back missing `wit`, forcing `|F_a| ≤ |F_c| < |F_a|`. -/
theorem not_aCReformulation
    (Φ : MILPReformulation P7.a.formulation P7.c.formulation)
    (hΦ : Φ.paramMap = paramMapAC) : False := by
  obtain ⟨pm, fwd, bwd, fwd_feas, bwd_feas, bwd_fwd, om, om_mono, fwd_obj, bwd_obj⟩ := Φ
  subst hΦ
  exact MILPReformulation.false_of_feasible_embeds_missing
    (F := P7.a.formulation) (G := P7.c.formulation)
    ⟨paramMapAC, fwd, bwd, fwd_feas, bwd_feas, bwd_fwd, om, om_mono, fwd_obj, bwd_obj⟩
    p3 (feasible_finite p3) incl incl_maps incl_inj wit wit_feasible wit_missing

end P7
