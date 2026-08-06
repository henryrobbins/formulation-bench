import Common
import problems.p3.formulations.a.Formulation
import problems.p3.formulations.c.Formulation

/-!
# `c` is not a reformulation of `a`

Formulation `c` represents every beaker count using two bounded decimal digits,
so every `c`-instance has only finitely many feasible points. Formulation `a`
has an instance with infinitely many feasible points. Its feasible set cannot
inject into any `c`-instance, regardless of the parameter mapping.
-/

namespace P3

private def pFree : P3.a.Params where
  NumBeakers := 1
  FlourAvailable := 0
  SpecialLiquidAvailable := 0
  MaxWasteAllowed := 0
  FlourUsagePerBeaker := fun _ => 0
  SpecialLiquidUsagePerBeaker := fun _ => 0
  SlimeProducedPerBeaker := fun _ => 0
  WasteProducedPerBeaker := fun _ => 0
  hNumBeakers := ⟨by omega⟩
  hFlour_nn := fun _ => le_refl 0
  hLiquid_nn := fun _ => le_refl 0
  hSlime_nn := fun _ => le_refl 0
  hWaste_nn := fun _ => le_refl 0

private def pt (n : ℕ) : P3.a.Vars pFree :=
  ⟨fun _ => n⟩

private lemma pt_feasible (n : ℕ) : P3.a.Feasible pFree (pt n) where
  hflour := by simp [pFree, pt]
  hliquid := by simp [pFree, pt]
  hwaste := by simp [pFree, pt]
  hNumBeakersUsed_nn := by simp [pt]

private lemma pt_injective : Function.Injective pt := by
  intro m n h
  let i : Fin pFree.NumBeakers := ⟨0, by simp [pFree]⟩
  have h' := congrFun (congrArg P3.a.Vars.NumBeakersUsed h) i
  simpa [pt] using h'

private lemma c_feasible_finite (q : P3.c.Params) :
    Set.Finite {v : P3.c.Vars q | P3.c.Feasible q v} := by
  classical
  let digitFns : Set (Fin q.N → ℤ) := {f | ∀ i, f i ∈ Set.Icc 0 9}
  let codes : Set ((Fin q.N → ℤ) × (Fin q.N → ℤ)) := digitFns ×ˢ digitFns
  let encode : P3.c.Vars q → (Fin q.N → ℤ) × (Fin q.N → ℤ) :=
    fun v => (v.n_0, v.n_1)
  have hdigit : digitFns.Finite := by
    simpa [digitFns] using Set.Finite.pi' (fun _ : Fin q.N => Set.finite_Icc (0 : ℤ) 9)
  have hcodes : codes.Finite := by
    simpa [codes] using hdigit.prod hdigit
  refine (hcodes.subset ?_).of_finite_image (f := encode) ?_
  · rintro x ⟨v, hv, hx⟩
    subst x
    exact ⟨fun i => ⟨hv.hn0_nn i, hv.hn0_hi i⟩,
      fun i => ⟨hv.hn1_nn i, hv.hn1_hi i⟩⟩
  · intro v _ w _ h
    cases v
    cases w
    simpa [encode] using h

theorem aCNotReformulation :
    IsEmpty (MILPReformulation P3.a.formulation P3.c.formulation) := by
  refine ⟨fun Φ => ?_⟩
  have htarget := c_feasible_finite (Φ.paramMap pFree)
  have himage : Set.Finite
      (Φ.fwd pFree '' {v : P3.a.Vars pFree | P3.a.Feasible pFree v}) :=
    htarget.subset (by
      rintro x ⟨v, hv, hx⟩
      subst x
      exact Φ.fwd_feas pFree v hv)
  have hsource : Set.Finite {v : P3.a.Vars pFree | P3.a.Feasible pFree v} :=
    himage.of_finite_image (Φ.fwd_injOn pFree)
  have hrange : (Set.range pt).Infinite := Set.infinite_range_of_injective pt_injective
  exact hrange (hsource.subset (by
    rintro x ⟨n, hn⟩
    subst x
    exact pt_feasible n))

end P3
