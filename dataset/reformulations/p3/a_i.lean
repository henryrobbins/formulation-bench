import Common
import problems.p3.formulations.a.Formulation
import problems.p3.formulations.i.Formulation

/-!
# `i` is not a reformulation of `a`

Formulation `i` replaces the objective by a constant, while formulation `a`
has an instance attaining two different objective values. Their images cannot
be equal under the strictly monotone `objMap`. This holds for any parameter
mapping.
-/

namespace P3

private def pTwo : P3.a.Params where
  NumBeakers := 1
  FlourAvailable := 1
  SpecialLiquidAvailable := 0
  MaxWasteAllowed := 0
  FlourUsagePerBeaker := fun _ => 1
  SpecialLiquidUsagePerBeaker := fun _ => 0
  SlimeProducedPerBeaker := fun _ => 1
  WasteProducedPerBeaker := fun _ => 0
  hNumBeakers := ⟨by omega⟩
  hFlour_nn := fun _ => zero_le_one
  hLiquid_nn := fun _ => le_refl 0
  hSlime_nn := fun _ => zero_le_one
  hWaste_nn := fun _ => le_refl 0

private def point (n : ℤ) : P3.a.Vars pTwo :=
  ⟨fun _ => n⟩

private lemma feasible_zero : P3.a.Feasible pTwo (point 0) where
  hflour := by simp [pTwo, point]
  hliquid := by simp [pTwo, point]
  hwaste := by simp [pTwo, point]
  hNumBeakersUsed_nn := by simp [point]

private lemma feasible_one : P3.a.Feasible pTwo (point 1) where
  hflour := by simp [pTwo, point]
  hliquid := by simp [pTwo, point]
  hwaste := by simp [pTwo, point]
  hNumBeakersUsed_nn := by simp [point]

private lemma obj_zero : P3.a.obj pTwo (point 0) = 0 := by
  simp [P3.a.obj, pTwo, point]

private lemma obj_one : P3.a.obj pTwo (point 1) = -1 := by
  simp [P3.a.obj, pTwo, point]

theorem aINotReformulation :
    IsEmpty (MILPReformulation P3.a.formulation P3.i.formulation) := by
  refine ⟨fun Φ => ?_⟩
  have h0 := Φ.fwd_obj pTwo (point 0) feasible_zero
  have h1 := Φ.fwd_obj pTwo (point 1) feasible_one
  change P3.i.obj (Φ.paramMap pTwo) (Φ.fwd pTwo (point 0)) =
    Φ.objMap (P3.a.obj pTwo (point 0)) at h0
  change P3.i.obj (Φ.paramMap pTwo) (Φ.fwd pTwo (point 1)) =
    Φ.objMap (P3.a.obj pTwo (point 1)) at h1
  rw [obj_zero] at h0
  rw [obj_one] at h1
  have heq : Φ.objMap 0 = Φ.objMap (-1) := by
    rw [← h0, ← h1]
    rfl
  have := Φ.objMap_mono.injective heq
  norm_num at this

end P3
