import Common
import problems.p2.formulations.a.Formulation
import problems.p2.formulations.i.Formulation

/-!
# `i` is not a reformulation of `a`

Formulation `i` replaces the objective by a constant, so it attains at most one
objective value on any instance. Formulation `a` has an instance attaining two
different objective values. Strict monotonicity of `objMap` makes identifying
their images impossible, for any parameter mapping.
-/

namespace P2

private def pTwo : P2.a.Params where
  NumExperiments := 1
  NumResources := 1
  ElectricityProduced := fun _ => 1
  ResourceRequired := fun _ _ => 1
  ResourceAvailable := fun _ => 1
  hNumExperiments := ⟨by omega⟩
  hNumResources := ⟨by omega⟩
  hElectricityProduced_nn := fun _ => zero_le_one
  hResourceRequired_nn := fun _ _ => zero_le_one
  hResourceAvailable_nn := fun _ => zero_le_one

private def point (n : ℤ) : P2.a.Vars pTwo :=
  ⟨fun _ => n⟩

private lemma feasible_zero : P2.a.Feasible pTwo (point 0) where
  hres := by simp [pTwo, point]
  hConductExperiment_nn := by simp [point]

private lemma feasible_one : P2.a.Feasible pTwo (point 1) where
  hres := by simp [pTwo, point]
  hConductExperiment_nn := by simp [point]

private lemma obj_zero : P2.a.obj pTwo (point 0) = 0 := by
  simp [P2.a.obj, pTwo, point]

private lemma obj_one : P2.a.obj pTwo (point 1) = -1 := by
  simp [P2.a.obj, pTwo, point]

theorem aINotReformulation :
    IsEmpty (MILPReformulation P2.a.formulation P2.i.formulation) := by
  refine ⟨fun Φ => ?_⟩
  have h0 := Φ.fwd_obj pTwo (point 0) feasible_zero
  have h1 := Φ.fwd_obj pTwo (point 1) feasible_one
  change P2.i.obj (Φ.paramMap pTwo) (Φ.fwd pTwo (point 0)) =
    Φ.objMap (P2.a.obj pTwo (point 0)) at h0
  change P2.i.obj (Φ.paramMap pTwo) (Φ.fwd pTwo (point 1)) =
    Φ.objMap (P2.a.obj pTwo (point 1)) at h1
  rw [obj_zero] at h0
  rw [obj_one] at h1
  have heq : Φ.objMap 0 = Φ.objMap (-1) := by
    rw [← h0, ← h1]
    rfl
  have := Φ.objMap_mono.injective heq
  norm_num at this

end P2
