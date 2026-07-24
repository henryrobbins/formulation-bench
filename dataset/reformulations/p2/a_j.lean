import Common
import problems.p2.formulations.a.Formulation
import problems.p2.formulations.j.Formulation

/-!
# `j` is not a reformulation of `a`

Formulation `j` relaxes the integer experiment counts to real variables. Its
feasible set and objective are convex, whereas formulation `a` has an instance
attaining exactly the two objective values `0` and `-1`. The midpoint of their
images creates a third attained objective value. This holds for any parameter
mapping.
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
    · intro k' _ hk'
      have hk'lt := k'.isLt
      have hilt := i.isLt
      change k'.val < 1 at hk'lt
      change i.val < 1 at hilt
      exact (hk' (Fin.ext (by omega))).elim
    · simp
  rw [hobj]
  have hx : v.ConductExperiment i = 0 ∨ v.ConductExperiment i = 1 := by omega
  rcases hx with hx | hx
  · rw [hx]
    norm_num
  · rw [hx]
    norm_num

private noncomputable def midpoint {q : P2.j.Params}
    (x y : P2.j.Vars q) : P2.j.Vars q :=
  ⟨fun i => (x.j i + y.j i) / 2⟩

private lemma midpoint_feasible {q : P2.j.Params} {x y : P2.j.Vars q}
    (hx : P2.j.Feasible q x) (hy : P2.j.Feasible q y) :
    P2.j.Feasible q (midpoint x y) where
  hres := by
    intro k
    have hxk := hx.hres k
    have hyk := hy.hres k
    calc
      ∑ i, q.I k i * (midpoint x y).j i =
          (1 / 2 : ℝ) * (∑ i, q.I k i * x.j i) +
            (1 / 2 : ℝ) * (∑ i, q.I k i * y.j i) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        simp only [midpoint]
        ring
      _ = ((∑ i, q.I k i * x.j i) + ∑ i, q.I k i * y.j i) / 2 := by ring
      _ ≤ q.Y k := by linarith
  hj_nn := by
    intro i
    simp only [midpoint]
    linarith [hx.hj_nn i, hy.hj_nn i]

private lemma midpoint_obj {q : P2.j.Params} (x y : P2.j.Vars q) :
    P2.j.obj q (midpoint x y) = (P2.j.obj q x + P2.j.obj q y) / 2 := by
  have hsum :
      (∑ i, q.A i * (midpoint x y).j i) =
        ((∑ i, q.A i * x.j i) + ∑ i, q.A i * y.j i) / 2 := by
    calc
      _ = (1 / 2 : ℝ) * (∑ i, q.A i * x.j i) +
          (1 / 2 : ℝ) * (∑ i, q.A i * y.j i) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        simp only [midpoint]
        ring
      _ = _ := by ring
  unfold P2.j.obj
  rw [hsum]
  ring

theorem aJNotReformulation :
    IsEmpty (MILPReformulation P2.a.formulation P2.j.formulation) := by
  refine ⟨fun Φ => ?_⟩
  let x := Φ.fwd pTwo (point 0)
  let y := Φ.fwd pTwo (point 1)
  have hx := Φ.fwd_feas pTwo (point 0) feasible_zero
  have hy := Φ.fwd_feas pTwo (point 1) feasible_one
  have hxobj := Φ.fwd_obj pTwo (point 0) feasible_zero
  have hyobj := Φ.fwd_obj pTwo (point 1) feasible_one
  change P2.j.obj (Φ.paramMap pTwo) x = Φ.objMap (P2.a.obj pTwo (point 0)) at hxobj
  change P2.j.obj (Φ.paramMap pTwo) y = Φ.objMap (P2.a.obj pTwo (point 1)) at hyobj
  rw [obj_zero] at hxobj
  rw [obj_one] at hyobj
  have hm := midpoint_feasible hx hy
  have hb := Φ.bwd_obj pTwo (midpoint x y) hm
  change P2.j.obj (Φ.paramMap pTwo) (midpoint x y) =
    Φ.objMap (P2.a.obj pTwo (Φ.bwd pTwo (midpoint x y))) at hb
  rw [midpoint_obj, hxobj, hyobj] at hb
  have hlt : Φ.objMap (-1) < Φ.objMap 0 := Φ.objMap_mono (by norm_num)
  rcases obj_eq_zero_or_neg_one _ (Φ.bwd_feas pTwo (midpoint x y) hm) with h | h
  · rw [h] at hb
    linarith
  · rw [h] at hb
    linarith

end P2
