import Common
import problems.p5.formulations.a.Formulation
import problems.p5.formulations.h.Formulation

/-!
# `h` is not a reformulation of `a`

Formulation `h` is continuous and convex. The midpoint of two feasible points
is feasible and attains their midpoint objective. Formulation `a` has an
instance attaining exactly `0` and `1`, so the midpoint of their distinct
images creates an impossible third value. This holds for any parameter mapping.
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

private lemma obj_eq_zero_or_one (v : P5.a.Vars pTwo) (h : P5.a.Feasible pTwo v) :
    P5.a.obj pTwo v = 0 ∨ P5.a.obj pTwo v = 1 := by
  have ht := h.htotal
  norm_num [pTwo] at ht
  have hsum_le : v.SubsoilBags + v.TopsoilBags ≤ 1 := by exact_mod_cast ht
  have hss := h.hss_nn
  have hts := h.hts_nn
  have hsum_nn : 0 ≤ v.SubsoilBags + v.TopsoilBags := by omega
  have hsum : v.SubsoilBags + v.TopsoilBags = 0 ∨
      v.SubsoilBags + v.TopsoilBags = 1 := by omega
  have hobj : P5.a.obj pTwo v =
      ((v.SubsoilBags + v.TopsoilBags : ℤ) : ℝ) := by
    simp [P5.a.obj, pTwo]
  rcases hsum with h | h <;> rw [hobj, h] <;> norm_num

private noncomputable def midpoint {q : P5.h.Params}
    (x y : P5.h.Vars q) : P5.h.Vars q :=
  ⟨(x.z + y.z) / 2, (x.g + y.g) / 2⟩

private lemma midpoint_feasible {q : P5.h.Params} {x y : P5.h.Vars q}
    (hx : P5.h.Feasible q x) (hy : P5.h.Feasible q y) :
    P5.h.Feasible q (midpoint x y) where
  hratio := by
    simp only [midpoint]
    linarith [hx.hratio, hy.hratio]
  hmin_vintage := by
    simp only [midpoint]
    linarith [hx.hmin_vintage, hy.hmin_vintage]
  hwine := by
    simp only [midpoint]
    linarith [hx.hwine, hy.hwine]
  hz_nn := by
    simp only [midpoint]
    linarith [hx.hz_nn, hy.hz_nn]
  hg_nn := by
    simp only [midpoint]
    linarith [hx.hg_nn, hy.hg_nn]

private lemma midpoint_obj {q : P5.h.Params} (x y : P5.h.Vars q) :
    P5.h.obj q (midpoint x y) = (P5.h.obj q x + P5.h.obj q y) / 2 := by
  simp [P5.h.obj, midpoint]
  ring

theorem aHNotReformulation :
    IsEmpty (MILPReformulation P5.a.formulation P5.h.formulation) := by
  refine ⟨fun Φ => ?_⟩
  let x := Φ.fwd pTwo ⟨0, 0⟩
  let y := Φ.fwd pTwo ⟨1, 0⟩
  have hx := Φ.fwd_feas pTwo ⟨0, 0⟩ feasible_zero
  have hy := Φ.fwd_feas pTwo ⟨1, 0⟩ feasible_one
  have hxobj := Φ.fwd_obj pTwo ⟨0, 0⟩ feasible_zero
  have hyobj := Φ.fwd_obj pTwo ⟨1, 0⟩ feasible_one
  change P5.h.obj (Φ.paramMap pTwo) x = Φ.objMap (P5.a.obj pTwo ⟨0, 0⟩) at hxobj
  change P5.h.obj (Φ.paramMap pTwo) y = Φ.objMap (P5.a.obj pTwo ⟨1, 0⟩) at hyobj
  norm_num [P5.a.obj, pTwo] at hxobj hyobj
  have hm := midpoint_feasible hx hy
  have hb := Φ.bwd_obj pTwo (midpoint x y) hm
  change P5.h.obj (Φ.paramMap pTwo) (midpoint x y) =
    Φ.objMap (P5.a.obj pTwo (Φ.bwd pTwo (midpoint x y))) at hb
  rw [midpoint_obj, hxobj, hyobj] at hb
  have hlt : Φ.objMap 0 < Φ.objMap 1 := Φ.objMap_mono (by norm_num)
  rcases obj_eq_zero_or_one _ (Φ.bwd_feas pTwo (midpoint x y) hm) with h | h
  · rw [h] at hb
    linarith
  · rw [h] at hb
    linarith

end P5
