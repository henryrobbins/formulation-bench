import Common
import problems.p1.formulations.a.Formulation
import problems.p1.formulations.c.Formulation

/-!
# `c` is not a reformulation of `a`

Formulation `c` encodes each machine count as two decimal digits, so every
feasible point has integer objective value at most `198`. Formulation `a` has
instances whose feasible objective values are all of `ℕ`. Since `objMap` is
strictly monotone, the `c`-objectives of the images of `0, 1, 2, …` form a
strictly increasing sequence of integers, which cannot stay below `198`. This
holds for any parameter mapping.
-/

namespace P1

-- ============================================================================
-- § Witness Instance
-- ============================================================================

/-- Nothing is required and nothing is consumed: every `(n, 0)` is feasible. -/
private def pFree : P1.a.Params where
  CashMachineProcessingRate := 0
  CardMachineProcessingRate := 0
  CashMachinePaperRolls := 0
  CardMachinePaperRolls := 0
  MinPeopleProcessed := 0
  MaxPaperRolls := 0
  hCashMachineProcessingRate_nn := le_refl 0
  hCardMachineProcessingRate_nn := le_refl 0
  hCashMachinePaperRolls_nn := le_refl 0
  hCardMachinePaperRolls_nn := le_refl 0
  hMinPeopleProcessed_nn := le_refl 0
  hMaxPaperRolls_nn := le_refl 0

private def pt (n : ℕ) : P1.a.Vars pFree := ⟨(n : ℤ), 0⟩

private lemma pt_feasible (n : ℕ) : P1.a.Feasible pFree (pt n) where
  hpeople := by norm_num [pFree, pt]
  hpaper := by norm_num [pFree, pt]
  hcard := by simp [pt]
  hNumCashMachines_nn := by simp [pt]
  hNumCardMachines_nn := le_refl 0

private lemma pt_obj (n : ℕ) : P1.a.obj pFree (pt n) = (n : ℝ) := by
  simp [P1.a.obj, pt]

-- ============================================================================
-- § The `c` Objective Is a Bounded Integer
-- ============================================================================

private def total {q : P1.c.Params} (v : P1.c.Vars q) : ℤ :=
  v.s_0 + 10 * v.s_1 + v.r_0 + 10 * v.r_1

private lemma total_obj {q : P1.c.Params} (v : P1.c.Vars q) :
    P1.c.obj q v = (total v : ℝ) := by
  simp [P1.c.obj, total]
  ring

private lemma total_nonneg {q : P1.c.Params} {v : P1.c.Vars q} (h : P1.c.Feasible q v) :
    0 ≤ total v := by
  have h1 := h.hs0_nn
  have h2 := h.hs1_nn
  have h3 := h.hr0_nn
  have h4 := h.hr1_nn
  simp only [total]
  omega

private lemma total_le {q : P1.c.Params} {v : P1.c.Vars q} (h : P1.c.Feasible q v) :
    total v ≤ 198 := by
  have h1 := h.hs0_hi
  have h2 := h.hs1_hi
  have h3 := h.hr0_hi
  have h4 := h.hr1_hi
  simp only [total]
  omega

-- ============================================================================
-- § Disproof
-- ============================================================================

theorem aCNotReformulation :
    IsEmpty (MILPReformulation P1.a.formulation P1.c.formulation) := by
  refine ⟨fun Φ => ?_⟩
  have hobjA : P1.a.formulation.obj = P1.a.obj := rfl
  have hobjC : P1.c.formulation.obj = P1.c.obj := rfl
  have hfeas : ∀ n : ℕ, P1.c.Feasible (Φ.paramMap pFree) (Φ.fwd pFree (pt n)) :=
    fun n => Φ.fwd_feas pFree (pt n) (pt_feasible n)
  -- The image of `(n, 0)` has `c`-objective `objMap n`.
  have hval : ∀ n : ℕ, ((total (Φ.fwd pFree (pt n)) : ℤ) : ℝ) = Φ.objMap n := by
    intro n
    have hf := Φ.fwd_obj pFree (pt n) (pt_feasible n)
    rw [hobjA, hobjC, total_obj, pt_obj] at hf
    exact hf
  -- Strict monotonicity of `objMap` makes that sequence strictly increasing.
  have hmono : ∀ k : ℕ, total (Φ.fwd pFree (pt k)) < total (Φ.fwd pFree (pt (k + 1))) := by
    intro k
    have h := Φ.objMap_mono (show ((k : ℝ)) < ((k + 1 : ℕ) : ℝ) by push_cast; linarith)
    rw [← hval k, ← hval (k + 1)] at h
    exact_mod_cast h
  -- A strictly increasing integer sequence starting at `≥ 0` outgrows `198`.
  have hge : ∀ n : ℕ, (n : ℤ) ≤ total (Φ.fwd pFree (pt n)) := by
    intro n
    induction n with
    | zero => simpa using total_nonneg (hfeas 0)
    | succ k ih =>
        have h := hmono k
        push_cast
        omega
  have hlo := hge 199
  have hhi := total_le (hfeas 199)
  norm_num at hlo
  omega

end P1
