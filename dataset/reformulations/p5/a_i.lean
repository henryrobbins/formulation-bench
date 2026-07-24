import Common
import problems.p5.formulations.a.Formulation
import problems.p5.formulations.i.Formulation

/-!
# `i` is not a reformulation of `a`

Formulation `i` has a constant objective. Formulation `a` has an instance
attaining both `0` and `1`, which a strictly monotone objective map must keep
distinct. This holds for any parameter mapping.
-/

namespace P5

private def pTwo : P5.a.Params where
  WaterSubsoil := 1
  WaterTopsoil := 1
  MaxTotalBags := 1
  MinTopsoilBags := 0
  MaxTopsoilProportion := 1
  hWaterSubsoil_nn := zero_le_one
  hWaterTopsoil_nn := zero_le_one
  hMaxTotalBags_nn := zero_le_one
  hMinTopsoilBags_nn := le_refl 0
  hMaxTopsoilProportion_nn := zero_le_one

private lemma feasible_zero : P5.a.Feasible pTwo ⟨0, 0⟩ where
  htotal := by norm_num [pTwo]
  hmin_top := by norm_num [pTwo]
  hprop := by norm_num [pTwo]
  hss_nn := le_refl 0
  hts_nn := le_refl 0

private lemma feasible_one : P5.a.Feasible pTwo ⟨1, 0⟩ where
  htotal := by norm_num [pTwo]
  hmin_top := by norm_num [pTwo]
  hprop := by norm_num [pTwo]
  hss_nn := zero_le_one
  hts_nn := le_refl 0

theorem aINotReformulation :
    IsEmpty (MILPReformulation P5.a.formulation P5.i.formulation) := by
  refine ⟨fun Φ => ?_⟩
  have h0 := Φ.fwd_obj pTwo ⟨0, 0⟩ feasible_zero
  have h1 := Φ.fwd_obj pTwo ⟨1, 0⟩ feasible_one
  change P5.i.obj (Φ.paramMap pTwo) (Φ.fwd pTwo ⟨0, 0⟩) =
    Φ.objMap (P5.a.obj pTwo ⟨0, 0⟩) at h0
  change P5.i.obj (Φ.paramMap pTwo) (Φ.fwd pTwo ⟨1, 0⟩) =
    Φ.objMap (P5.a.obj pTwo ⟨1, 0⟩) at h1
  norm_num [P5.a.obj, pTwo] at h0 h1
  have heq : Φ.objMap 0 = Φ.objMap 1 := by
    rw [← h0, ← h1]
    rfl
  have := Φ.objMap_mono.injective heq
  norm_num at this

end P5
