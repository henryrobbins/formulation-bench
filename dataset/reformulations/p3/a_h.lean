import Common
import problems.p3.formulations.a.Formulation
import problems.p3.formulations.h.Formulation

/-!
# `h` is not a reformulation of `a`

Formulation `h` is continuous and convex, so the midpoint of two feasible
points is feasible and attains the midpoint of their objectives. Formulation
`a` has an instance attaining exactly `0` and `-1`; the midpoint of their
distinct images is neither image. This holds for any parameter mapping.
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

private lemma obj_eq_zero_or_neg_one (v : P3.a.Vars pTwo) (h : P3.a.Feasible pTwo v) :
    P3.a.obj pTwo v = 0 ∨ P3.a.obj pTwo v = -1 := by
  let i : Fin pTwo.NumBeakers := ⟨0, by simp [pTwo]⟩
  have hle : (v.NumBeakersUsed i : ℝ) ≤ 1 := by
    simpa [pTwo, i] using h.hflour
  have hle' : v.NumBeakersUsed i ≤ 1 := by exact_mod_cast hle
  have hnn := h.hNumBeakersUsed_nn i
  have hobj : P3.a.obj pTwo v = -(v.NumBeakersUsed i : ℝ) := by
    unfold P3.a.obj
    rw [Finset.sum_eq_single i]
    · simp [pTwo]
    · intro j _ hji
      have hj := j.isLt
      have hi := i.isLt
      change j.val < 1 at hj
      change i.val < 1 at hi
      exact (hji (Fin.ext (by omega))).elim
    · simp
  rw [hobj]
  have hx : v.NumBeakersUsed i = 0 ∨ v.NumBeakersUsed i = 1 := by omega
  rcases hx with hx | hx
  · rw [hx]
    norm_num
  · rw [hx]
    norm_num

private noncomputable def midpoint {q : P3.h.Params}
    (x y : P3.h.Vars q) : P3.h.Vars q :=
  ⟨(x.e + y.e) / 2, (x.h + y.h) / 2⟩

private lemma midpoint_feasible {q : P3.h.Params} {x y : P3.h.Vars q}
    (hx : P3.h.Feasible q x) (hy : P3.h.Feasible q y) :
    P3.h.Feasible q (midpoint x y) where
  hheating := by
    simp only [midpoint]
    linarith [hx.hheating, hy.hheating]
  hcooling := by
    simp only [midpoint]
    linarith [hx.hcooling, hy.hcooling]
  he_nn := by
    simp only [midpoint]
    linarith [hx.he_nn, hy.he_nn]
  hh_nn := by
    simp only [midpoint]
    linarith [hx.hh_nn, hy.hh_nn]

private lemma midpoint_obj {q : P3.h.Params} (x y : P3.h.Vars q) :
    P3.h.obj q (midpoint x y) = (P3.h.obj q x + P3.h.obj q y) / 2 := by
  simp [P3.h.obj, midpoint]
  ring

theorem aHNotReformulation :
    IsEmpty (MILPReformulation P3.a.formulation P3.h.formulation) := by
  refine ⟨fun Φ => ?_⟩
  let x := Φ.fwd pTwo (point 0)
  let y := Φ.fwd pTwo (point 1)
  have hx := Φ.fwd_feas pTwo (point 0) feasible_zero
  have hy := Φ.fwd_feas pTwo (point 1) feasible_one
  have hxobj := Φ.fwd_obj pTwo (point 0) feasible_zero
  have hyobj := Φ.fwd_obj pTwo (point 1) feasible_one
  change P3.h.obj (Φ.paramMap pTwo) x = Φ.objMap (P3.a.obj pTwo (point 0)) at hxobj
  change P3.h.obj (Φ.paramMap pTwo) y = Φ.objMap (P3.a.obj pTwo (point 1)) at hyobj
  rw [obj_zero] at hxobj
  rw [obj_one] at hyobj
  have hm := midpoint_feasible hx hy
  have hb := Φ.bwd_obj pTwo (midpoint x y) hm
  change P3.h.obj (Φ.paramMap pTwo) (midpoint x y) =
    Φ.objMap (P3.a.obj pTwo (Φ.bwd pTwo (midpoint x y))) at hb
  rw [midpoint_obj, hxobj, hyobj] at hb
  have hlt : Φ.objMap (-1) < Φ.objMap 0 := Φ.objMap_mono (by norm_num)
  rcases obj_eq_zero_or_neg_one _ (Φ.bwd_feas pTwo (midpoint x y) hm) with h | h
  · rw [h] at hb
    linarith
  · rw [h] at hb
    linarith

end P3
