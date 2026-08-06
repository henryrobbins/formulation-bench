import Common
import problems.p2.formulations.a.Formulation
import problems.p2.formulations.c.Formulation

/-!
# `c` is not a reformulation of `a`

Formulation `c` represents every experiment count using two bounded decimal
digits. Consequently, every `c`-instance has only finitely many feasible
points. Formulation `a` has an instance with infinitely many feasible points,
which cannot inject into any `c`-instance. This holds for any parameter
mapping.
-/

namespace P2

-- ============================================================================
-- § Witness Instance
-- ============================================================================

private def pFree : P2.a.Params where
  NumExperiments := 1
  NumResources := 1
  ElectricityProduced := fun _ => 0
  ResourceRequired := fun _ _ => 0
  ResourceAvailable := fun _ => 0
  hNumExperiments := ⟨by omega⟩
  hNumResources := ⟨by omega⟩
  hElectricityProduced_nn := fun _ => le_refl 0
  hResourceRequired_nn := fun _ _ => le_refl 0
  hResourceAvailable_nn := fun _ => le_refl 0

private def pt (n : ℕ) : P2.a.Vars pFree :=
  ⟨fun _ => n⟩

private lemma pt_feasible (n : ℕ) : P2.a.Feasible pFree (pt n) where
  hres := by simp [pFree, pt]
  hConductExperiment_nn := by simp [pt]

private lemma pt_injective : Function.Injective pt := by
  intro m n h
  let i : Fin pFree.NumExperiments := ⟨0, by simp [pFree]⟩
  have h' := congrFun (congrArg P2.a.Vars.ConductExperiment h) i
  simpa [pt] using h'

-- ============================================================================
-- § Finiteness of the `c` Feasible Set
-- ============================================================================

private lemma c_feasible_finite (q : P2.c.Params) :
    Set.Finite {v : P2.c.Vars q | P2.c.Feasible q v} := by
  classical
  let digitFns : Set (Fin q.M → ℤ) := {f | ∀ i, f i ∈ Set.Icc 0 9}
  let codes : Set ((Fin q.M → ℤ) × (Fin q.M → ℤ)) := digitFns ×ˢ digitFns
  let encode : P2.c.Vars q → (Fin q.M → ℤ) × (Fin q.M → ℤ) :=
    fun v => (v.j_0, v.j_1)
  have hdigit : digitFns.Finite := by
    simpa [digitFns] using Set.Finite.pi' (fun _ : Fin q.M => Set.finite_Icc (0 : ℤ) 9)
  have hcodes : codes.Finite := by
    simpa [codes] using hdigit.prod hdigit
  refine (hcodes.subset ?_).of_finite_image (f := encode) ?_
  · rintro x ⟨v, hv, hx⟩
    subst x
    exact ⟨fun i => ⟨hv.hj0_nn i, hv.hj0_hi i⟩,
      fun i => ⟨hv.hj1_nn i, hv.hj1_hi i⟩⟩
  · intro v _ w _ h
    cases v
    cases w
    simpa [encode] using h

-- ============================================================================
-- § Disproof
-- ============================================================================

theorem aCNotReformulation :
    IsEmpty (MILPReformulation P2.a.formulation P2.c.formulation) := by
  refine ⟨fun Φ => ?_⟩
  have htarget : Set.Finite
      {v : P2.c.Vars (Φ.paramMap pFree) | P2.c.Feasible (Φ.paramMap pFree) v} :=
    c_feasible_finite _
  have himage : Set.Finite
      (Φ.fwd pFree '' {v : P2.a.Vars pFree | P2.a.Feasible pFree v}) :=
    htarget.subset (by
      rintro x ⟨v, hv, hx⟩
      subst x
      exact Φ.fwd_feas pFree v hv)
  have hsource : Set.Finite {v : P2.a.Vars pFree | P2.a.Feasible pFree v} :=
    himage.of_finite_image (Φ.fwd_injOn pFree)
  have hrange : (Set.range pt).Infinite := Set.infinite_range_of_injective pt_injective
  exact hrange (hsource.subset (by
    rintro x ⟨n, hn⟩
    subst x
    exact pt_feasible n))

end P2
