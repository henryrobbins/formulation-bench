import Common
import problems.p1.formulations.a.Formulation
import problems.p1.formulations.h.Formulation

/-!
# `h` is not a reformulation of `a`

Formulation `h` has no upper bound on either variable: adding a container to a
feasible point keeps it feasible and raises the objective by one, so a nonempty
`h`-instance attains infinitely many objective values. Formulation `a` has
instances attaining only two, and `objMap` is a bijection between the attained
value sets (`MILPReformulation.objMap_bijOn`). Three `h`-feasible points then
carry three distinct values into a two-element set. This holds for any
parameter mapping.
-/

namespace P1

-- ============================================================================
-- § Witness Instance
-- ============================================================================

/-- One paper roll per machine and one roll available: the feasible set is
`{(0, 0), (1, 0)}`, attaining the two objective values `0` and `1`. -/
private def pTwo : P1.a.Params where
  CashMachineProcessingRate := 0
  CardMachineProcessingRate := 0
  CashMachinePaperRolls := 1
  CardMachinePaperRolls := 1
  MinPeopleProcessed := 0
  MaxPaperRolls := 1
  hCashMachineProcessingRate_nn := le_refl 0
  hCardMachineProcessingRate_nn := le_refl 0
  hCashMachinePaperRolls_nn := zero_le_one
  hCardMachinePaperRolls_nn := zero_le_one
  hMinPeopleProcessed_nn := le_refl 0
  hMaxPaperRolls_nn := zero_le_one

private lemma feasible_zero : P1.a.Feasible pTwo ⟨0, 0⟩ where
  hpeople := by norm_num [pTwo]
  hpaper := by norm_num [pTwo]
  hcard := le_refl 0
  hNumCashMachines_nn := le_refl 0
  hNumCardMachines_nn := le_refl 0

/-- Only two objective values are attained on the witness instance. -/
private lemma obj_eq_zero_or_one (v : P1.a.Vars pTwo) (h : P1.a.Feasible pTwo v) :
    P1.a.obj pTwo v = 0 ∨ P1.a.obj pTwo v = 1 := by
  have hp := h.hpaper
  have hs := h.hNumCashMachines_nn
  have hr := h.hNumCardMachines_nn
  norm_num [pTwo] at hp
  have hz : v.NumCashMachines + v.NumCardMachines ≤ 1 := by exact_mod_cast hp
  have hsum : v.NumCashMachines + v.NumCardMachines = 0 ∨
      v.NumCashMachines + v.NumCardMachines = 1 := by omega
  have hcast : P1.a.obj pTwo v = ((v.NumCashMachines + v.NumCardMachines : ℤ) : ℝ) := by
    simp [P1.a.obj]
  rcases hsum with h' | h' <;> rw [hcast, h'] <;> norm_num

-- ============================================================================
-- § Adding a Container Preserves `h`-Feasibility
-- ============================================================================

private def shift {q : P1.h.Params} (v : P1.h.Vars q) (n : ℕ) : P1.h.Vars q :=
  ⟨v.c + n, v.p⟩

private lemma shift_feasible {q : P1.h.Params} {v : P1.h.Vars q}
    (h : P1.h.Feasible q v) (n : ℕ) : P1.h.Feasible q (shift v n) where
  htruck_ratio := by
    have hn : (0 : ℝ) ≤ q.K * n := mul_nonneg q.hK_nn (Nat.cast_nonneg n)
    have := h.htruck_ratio
    simp only [shift]
    push_cast
    nlinarith [q.hK_nn]
  hmin_cont := by
    have := h.hmin_cont
    simp only [shift]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]
  hoil := by
    have hn : (0 : ℝ) ≤ q.G * n := mul_nonneg q.hG_nn (Nat.cast_nonneg n)
    have := h.hoil
    simp only [shift]
    push_cast
    nlinarith
  hc_nn := by
    have := h.hc_nn
    simp only [shift]
    positivity
  hp_nn := h.hp_nn

private lemma shift_obj {q : P1.h.Params} (v : P1.h.Vars q) (n : ℕ) :
    P1.h.obj q (shift v n) = (v.c : ℝ) + (v.p : ℝ) + n := by
  simp only [shift, P1.h.obj]
  push_cast
  ring

-- ============================================================================
-- § Disproof
-- ============================================================================

theorem aHNotReformulation :
    IsEmpty (MILPReformulation P1.a.formulation P1.h.formulation) := by
  refine ⟨fun Φ => ?_⟩
  have hobjA : P1.a.formulation.obj = P1.a.obj := rfl
  have hobjH : P1.h.formulation.obj = P1.h.obj := rfl
  -- A feasible `h`-point exists, since `a` is feasible on the witness instance.
  obtain ⟨v, hv⟩ : ∃ y : P1.h.Vars (Φ.paramMap pTwo), P1.h.Feasible (Φ.paramMap pTwo) y :=
    ⟨Φ.fwd pTwo ⟨0, 0⟩, Φ.fwd_feas pTwo ⟨0, 0⟩ feasible_zero⟩
  -- Every shifted point's objective is the image of an `a`-objective, hence one
  -- of two values.
  have key : ∀ n : ℕ, (v.c : ℝ) + (v.p : ℝ) + n = Φ.objMap 0 ∨
      (v.c : ℝ) + (v.p : ℝ) + n = Φ.objMap 1 := by
    intro n
    have hb := Φ.bwd_obj pTwo (shift v n) (shift_feasible hv n)
    rw [hobjA, hobjH] at hb
    have hs := shift_obj v n
    rcases obj_eq_zero_or_one _ (Φ.bwd_feas pTwo (shift v n) (shift_feasible hv n))
      with h' | h'
    · exact Or.inl (by rw [← hs, hb, h'])
    · exact Or.inr (by rw [← hs, hb, h'])
  have h0 := key 0
  have h1 := key 1
  have h2 := key 2
  push_cast at h0 h1 h2
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> linarith

end P1
