import Common
import problems.p2.formulations.a.Formulation
import problems.p2.formulations.h.Formulation

/-!
# `h` is not a reformulation of `a`

Formulation `h` is a continuous linear model, so the midpoint of two feasible
points is feasible and has the midpoint of their objective values. Formulation
`a` has an instance attaining exactly the two objective values `0` and `-1`.
The images of those values are distinct, while their midpoint cannot be the
image of either one. This holds for any parameter mapping.
-/

namespace P2

-- ============================================================================
-- § Witness Instance
-- ============================================================================

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

private lemma obj_eq_zero_or_neg_one (v : P2.a.Vars pTwo) (h : P2.a.Feasible pTwo v) :
    P2.a.obj pTwo v = 0 ∨ P2.a.obj pTwo v = -1 := by
  let i : Fin pTwo.NumExperiments := ⟨0, by simp [pTwo]⟩
  let k : Fin pTwo.NumResources := ⟨0, by simp [pTwo]⟩
  have hle : (v.ConductExperiment i : ℝ) ≤ 1 := by
    simpa [pTwo, i, k] using h.hres k
  have hle' : v.ConductExperiment i ≤ 1 := by exact_mod_cast hle
  have hnn := h.hConductExperiment_nn i
  have hobj : P2.a.obj pTwo v = -(v.ConductExperiment i : ℝ) := by
    unfold P2.a.obj
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
  have hx : v.ConductExperiment i = 0 ∨ v.ConductExperiment i = 1 := by
    omega
  rcases hx with hx | hx
  · rw [hx]
    norm_num
  · rw [hx]
    norm_num

-- ============================================================================
-- § Midpoints in `h`
-- ============================================================================

private noncomputable def midpoint {q : P2.h.Params} (x y : P2.h.Vars q) : P2.h.Vars q :=
  ⟨(x.n + y.n) / 2, (x.v + y.v) / 2⟩

private lemma midpoint_feasible {q : P2.h.Params} {x y : P2.h.Vars q}
    (hx : P2.h.Feasible q x) (hy : P2.h.Feasible q y) :
    P2.h.Feasible q (midpoint x y) where
  hcat := by
    simp only [midpoint]
    linarith [hx.hcat, hy.hcat]
  hgold := by
    simp only [midpoint]
    linarith [hx.hgold, hy.hgold]
  hn_nn := by
    simp only [midpoint]
    linarith [hx.hn_nn, hy.hn_nn]
  hv_nn := by
    simp only [midpoint]
    linarith [hx.hv_nn, hy.hv_nn]

private lemma midpoint_obj {q : P2.h.Params} (x y : P2.h.Vars q) :
    P2.h.obj q (midpoint x y) = (P2.h.obj q x + P2.h.obj q y) / 2 := by
  simp [P2.h.obj, midpoint]
  ring

-- ============================================================================
-- § Disproof
-- ============================================================================

theorem aHNotReformulation :
    IsEmpty (MILPReformulation P2.a.formulation P2.h.formulation) := by
  refine ⟨fun Φ => ?_⟩
  let x := Φ.fwd pTwo (point 0)
  let y := Φ.fwd pTwo (point 1)
  have hx : P2.h.Feasible (Φ.paramMap pTwo) x :=
    Φ.fwd_feas pTwo (point 0) feasible_zero
  have hy : P2.h.Feasible (Φ.paramMap pTwo) y :=
    Φ.fwd_feas pTwo (point 1) feasible_one
  have hxobj : P2.h.obj (Φ.paramMap pTwo) x = Φ.objMap 0 := by
    have h := Φ.fwd_obj pTwo (point 0) feasible_zero
    change P2.h.obj (Φ.paramMap pTwo) x = Φ.objMap (P2.a.obj pTwo (point 0)) at h
    simpa [obj_zero] using h
  have hyobj : P2.h.obj (Φ.paramMap pTwo) y = Φ.objMap (-1) := by
    have h := Φ.fwd_obj pTwo (point 1) feasible_one
    change P2.h.obj (Φ.paramMap pTwo) y = Φ.objMap (P2.a.obj pTwo (point 1)) at h
    simpa [obj_one] using h
  have hm := midpoint_feasible hx hy
  have hb := Φ.bwd_obj pTwo (midpoint x y) hm
  rw [show P2.a.formulation.obj = P2.a.obj from rfl,
    show P2.h.formulation.obj = P2.h.obj from rfl, midpoint_obj, hxobj, hyobj] at hb
  have hlt : Φ.objMap (-1) < Φ.objMap 0 := Φ.objMap_mono (by norm_num)
  rcases obj_eq_zero_or_neg_one _ (Φ.bwd_feas pTwo (midpoint x y) hm) with h | h
  · rw [h] at hb
    linarith
  · rw [h] at hb
    linarith

end P2
