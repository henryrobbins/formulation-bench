import Common
import problems.p4.formulations.a.Formulation
import problems.p4.formulations.i.Formulation

/-!
# `i` is not a reformulation of `a`

Formulation `i` has a constant objective. Formulation `a` has an instance
attaining the two distinct values `0` and `1`, whose images must remain
distinct under the strictly monotone `objMap`. This holds for any parameter
mapping.
-/

namespace P4

private def pTwo : P4.a.Params where
  CarCapacity := 0
  CarPollution := 0
  BusCapacity := 0
  BusPollution := 1
  MinEmployeesToTransport := 0
  MaxBuses := 1
  hCarCapacity_nn := le_refl 0
  hCarPollution_nn := le_refl 0
  hBusCapacity_nn := le_refl 0
  hBusPollution_nn := zero_le_one
  hMinEmployeesToTransport_nn := le_refl 0
  hMaxBuses_nn := zero_le_one

private lemma feasible_zero : P4.a.Feasible pTwo ⟨0, 0⟩ where
  htransport := by norm_num [pTwo]
  hmaxbus := by norm_num [pTwo]
  hcars_nn := le_refl 0
  hbus_nn := le_refl 0

private lemma feasible_one : P4.a.Feasible pTwo ⟨0, 1⟩ where
  htransport := by norm_num [pTwo]
  hmaxbus := by norm_num [pTwo]
  hcars_nn := le_refl 0
  hbus_nn := zero_le_one

theorem aINotReformulation :
    IsEmpty (MILPReformulation P4.a.formulation P4.i.formulation) := by
  refine ⟨fun Φ => ?_⟩
  have h0 := Φ.fwd_obj pTwo ⟨0, 0⟩ feasible_zero
  have h1 := Φ.fwd_obj pTwo ⟨0, 1⟩ feasible_one
  change P4.i.obj (Φ.paramMap pTwo) (Φ.fwd pTwo ⟨0, 0⟩) =
    Φ.objMap (P4.a.obj pTwo ⟨0, 0⟩) at h0
  change P4.i.obj (Φ.paramMap pTwo) (Φ.fwd pTwo ⟨0, 1⟩) =
    Φ.objMap (P4.a.obj pTwo ⟨0, 1⟩) at h1
  norm_num [P4.a.obj, pTwo] at h0 h1
  have heq : Φ.objMap 0 = Φ.objMap 1 := by
    rw [← h0, ← h1]
    rfl
  have := Φ.objMap_mono.injective heq
  norm_num at this

end P4
