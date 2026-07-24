import Common
import problems.p5.formulations.a.Formulation
import problems.p5.formulations.j.Formulation

/-!
# `j` is not a reformulation of `a`

Formulation `j` drops the total-bag and minimum-topsoil constraints, making the
origin feasible on every instance. Formulation `a` has an infeasible instance,
so backward feasibility fails for any parameter mapping.
-/

namespace P5

private def pEmpty : P5.a.Params where
  WaterSubsoil := 0
  WaterTopsoil := 0
  MaxTotalBags := 0
  MinTopsoilBags := 1
  MaxTopsoilProportion := 0
  hWaterSubsoil_nn := le_refl 0
  hWaterTopsoil_nn := le_refl 0
  hMaxTotalBags_nn := le_refl 0
  hMinTopsoilBags_nn := zero_le_one
  hMaxTopsoilProportion_nn := le_refl 0

private lemma pEmpty_infeasible (v : P5.a.Vars pEmpty) : ¬ P5.a.Feasible pEmpty v := by
  intro h
  have ht := h.htotal
  have hm := h.hmin_top
  have hs := h.hss_nn
  norm_num [pEmpty] at ht hm
  have hs' : (0 : ℝ) ≤ v.SubsoilBags := by exact_mod_cast hs
  linarith

private def origin (q : P5.j.Params) : P5.j.Vars q :=
  ⟨0, 0⟩

private lemma origin_feasible (q : P5.j.Params) : P5.j.Feasible q (origin q) where
  hprop := by simp [origin]
  hh_nn := le_refl 0
  hd_nn := le_refl 0

theorem aJNotReformulation :
    IsEmpty (MILPReformulation P5.a.formulation P5.j.formulation) :=
  ⟨fun Φ => pEmpty_infeasible _
    (Φ.bwd_feas pEmpty (origin _) (origin_feasible _))⟩

end P5
