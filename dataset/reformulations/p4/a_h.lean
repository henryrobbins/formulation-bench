import Common
import problems.p4.formulations.a.Formulation
import problems.p4.formulations.h.Formulation

/-!
# `h` is not a reformulation of `a`

Formulation `h` is continuous and convex, so a midpoint of feasible points is
feasible and attains the midpoint objective. Formulation `a` has an instance
attaining exactly `0` and `1`; the midpoint of their distinct images creates a
third value. This holds for any parameter mapping.
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

private lemma obj_eq_zero_or_one (v : P4.a.Vars pTwo) (h : P4.a.Feasible pTwo v) :
    P4.a.obj pTwo v = 0 ∨ P4.a.obj pTwo v = 1 := by
  have hleR := h.hmaxbus
  norm_num [pTwo] at hleR
  have hle : v.xBuses ≤ 1 := by
    exact_mod_cast hleR
  have hnn := h.hbus_nn
  have hx : v.xBuses = 0 ∨ v.xBuses = 1 := by omega
  rcases hx with hx | hx <;> simp [P4.a.obj, pTwo, hx]

private noncomputable def midpoint {q : P4.h.Params}
    (x y : P4.h.Vars q) : P4.h.Vars q :=
  ⟨(x.e + y.e) / 2, (x.p + y.p) / 2, (x.a + y.a) / 2⟩

private lemma midpoint_feasible {q : P4.h.Params} {x y : P4.h.Vars q}
    (hx : P4.h.Feasible q x) (hy : P4.h.Feasible q y) :
    P4.h.Feasible q (midpoint x y) where
  hcanoe_frac := by
    simp only [midpoint]
    linarith [hx.hcanoe_frac, hy.hcanoe_frac]
  htime := by
    simp only [midpoint]
    linarith [hx.htime, hy.htime]
  hmin_runners := by
    simp only [midpoint]
    linarith [hx.hmin_runners, hy.hmin_runners]
  he_nn := by
    simp only [midpoint]
    linarith [hx.he_nn, hy.he_nn]
  hp_nn := by
    simp only [midpoint]
    linarith [hx.hp_nn, hy.hp_nn]
  ha_nn := by
    simp only [midpoint]
    linarith [hx.ha_nn, hy.ha_nn]

private lemma midpoint_obj {q : P4.h.Params} (x y : P4.h.Vars q) :
    P4.h.obj q (midpoint x y) = (P4.h.obj q x + P4.h.obj q y) / 2 := by
  simp [P4.h.obj, midpoint]
  ring

theorem aHNotReformulation :
    IsEmpty (MILPReformulation P4.a.formulation P4.h.formulation) := by
  refine ⟨fun Φ => ?_⟩
  let x := Φ.fwd pTwo ⟨0, 0⟩
  let y := Φ.fwd pTwo ⟨0, 1⟩
  have hx := Φ.fwd_feas pTwo ⟨0, 0⟩ feasible_zero
  have hy := Φ.fwd_feas pTwo ⟨0, 1⟩ feasible_one
  have hxobj := Φ.fwd_obj pTwo ⟨0, 0⟩ feasible_zero
  have hyobj := Φ.fwd_obj pTwo ⟨0, 1⟩ feasible_one
  change P4.h.obj (Φ.paramMap pTwo) x = Φ.objMap (P4.a.obj pTwo ⟨0, 0⟩) at hxobj
  change P4.h.obj (Φ.paramMap pTwo) y = Φ.objMap (P4.a.obj pTwo ⟨0, 1⟩) at hyobj
  norm_num [P4.a.obj, pTwo] at hxobj hyobj
  have hm := midpoint_feasible hx hy
  have hb := Φ.bwd_obj pTwo (midpoint x y) hm
  change P4.h.obj (Φ.paramMap pTwo) (midpoint x y) =
    Φ.objMap (P4.a.obj pTwo (Φ.bwd pTwo (midpoint x y))) at hb
  rw [midpoint_obj, hxobj, hyobj] at hb
  have hlt : Φ.objMap 0 < Φ.objMap 1 := Φ.objMap_mono (by norm_num)
  rcases obj_eq_zero_or_one _ (Φ.bwd_feas pTwo (midpoint x y) hm) with h | h
  · rw [h] at hb
    linarith
  · rw [h] at hb
    linarith

end P4
