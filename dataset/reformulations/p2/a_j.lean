import Common
import problems.p2.formulations.a.Formulation
import problems.p2.formulations.j.Formulation

/-!
# `j` is not a reformulation of `a`

Formulation `j` omits the resource-capacity constraint. Formulation `a` has an
instance attaining exactly the two objective values `0` and `-1`, while any
target instance capable of representing both values has an unbounded feasible
objective ray. Three points on that ray cannot all map back to those two
strictly ordered objective values. This holds for any parameter mapping.
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

private def targetPoint (q : P2.j.Params) (i : Fin q.M) (n : ℤ) : P2.j.Vars q :=
  ⟨fun j => if j = i then n else 0⟩

private lemma targetPoint_feasible (q : P2.j.Params) (i : Fin q.M) {n : ℤ}
    (hn : 0 ≤ n) : P2.j.Feasible q (targetPoint q i n) where
  hj_nn := by
    intro j
    simp [targetPoint]
    split_ifs <;> omega

private lemma targetPoint_obj (q : P2.j.Params) (i : Fin q.M) (n : ℤ) :
    P2.j.obj q (targetPoint q i n) = -q.A i * n := by
  simp [P2.j.obj, targetPoint]

theorem aJNotReformulation :
    IsEmpty (MILPReformulation P2.a.formulation P2.j.formulation) := by
  refine ⟨fun Φ => ?_⟩
  let q := Φ.paramMap pTwo
  have hlt : Φ.objMap (-1) < Φ.objMap 0 := Φ.objMap_mono (by norm_num)
  have hA : ∃ i : Fin q.M, 0 < q.A i := by
    by_contra h
    push_neg at h
    have hobj : ∀ z : P2.j.Vars q, P2.j.obj q z = 0 := by
      intro z
      have hzero : ∀ i : Fin q.M, q.A i = 0 := fun i =>
        le_antisymm (h i) (q.hA_nn i)
      simp [P2.j.obj, hzero]
    have hzero := Φ.fwd_obj pTwo (point 0) feasible_zero
    have hone := Φ.fwd_obj pTwo (point 1) feasible_one
    change P2.j.obj q (Φ.fwd pTwo (point 0)) = Φ.objMap (P2.a.obj pTwo (point 0)) at hzero
    change P2.j.obj q (Φ.fwd pTwo (point 1)) = Φ.objMap (P2.a.obj pTwo (point 1)) at hone
    rw [obj_zero] at hzero
    rw [obj_one] at hone
    rw [hobj] at hzero hone
    linarith
  obtain ⟨i, hi⟩ := hA
  let z0 := targetPoint q i 0
  let z1 := targetPoint q i 1
  let z2 := targetPoint q i 2
  have hz0 := targetPoint_feasible q i (by omega : (0 : ℤ) ≤ 0)
  have hz1 := targetPoint_feasible q i (by omega : (0 : ℤ) ≤ 1)
  have hz2 := targetPoint_feasible q i (by omega : (0 : ℤ) ≤ 2)
  have hb0 := Φ.bwd_obj pTwo z0 hz0
  have hb1 := Φ.bwd_obj pTwo z1 hz1
  have hb2 := Φ.bwd_obj pTwo z2 hz2
  change P2.j.obj q z0 = Φ.objMap (P2.a.obj pTwo (Φ.bwd pTwo z0)) at hb0
  change P2.j.obj q z1 = Φ.objMap (P2.a.obj pTwo (Φ.bwd pTwo z1)) at hb1
  change P2.j.obj q z2 = Φ.objMap (P2.a.obj pTwo (Φ.bwd pTwo z2)) at hb2
  simp only [z0, targetPoint_obj, Int.cast_zero, mul_zero] at hb0
  simp only [z1, targetPoint_obj, Int.cast_one, mul_one] at hb1
  simp only [z2, targetPoint_obj, Int.cast_ofNat] at hb2
  have hs0 := obj_eq_zero_or_neg_one _ (Φ.bwd_feas pTwo z0 hz0)
  have hs1 := obj_eq_zero_or_neg_one _ (Φ.bwd_feas pTwo z1 hz1)
  have hs2 := obj_eq_zero_or_neg_one _ (Φ.bwd_feas pTwo z2 hz2)
  rcases hs0 with h0 | h0 <;> rcases hs1 with h1 | h1 <;> rcases hs2 with h2 | h2 <;>
    rw [h0] at hb0 <;> rw [h1] at hb1 <;> rw [h2] at hb2 <;> linarith

end P2
