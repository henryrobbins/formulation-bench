import Common
import problems.p1.formulations.a.Formulation
import problems.p1.formulations.j.Formulation

/-!
# `j` is not a reformulation of `a`

Formulation `j` drops the throughput constraint, so its feasible set contains
the origin on *every* instance. Formulation `a` has instances with an empty
feasible set. Backward feasibility then fails for any candidate reformulation,
whatever the parameter mapping.
-/

namespace P1

-- ============================================================================
-- § Witness Instance
-- ============================================================================

/-- Neither machine processes anybody, yet a person must be processed. -/
private def pEmpty : P1.a.Params where
  CashMachineProcessingRate := 0
  CardMachineProcessingRate := 0
  CashMachinePaperRolls := 0
  CardMachinePaperRolls := 0
  MinPeopleProcessed := 1
  MaxPaperRolls := 0
  hCashMachineProcessingRate_nn := le_refl 0
  hCardMachineProcessingRate_nn := le_refl 0
  hCashMachinePaperRolls_nn := le_refl 0
  hCardMachinePaperRolls_nn := le_refl 0
  hMinPeopleProcessed_nn := zero_le_one
  hMaxPaperRolls_nn := le_refl 0

private lemma pEmpty_infeasible (v : P1.a.Vars pEmpty) : ¬ P1.a.Feasible pEmpty v := by
  intro h
  have := h.hpeople
  norm_num [pEmpty] at this

-- ============================================================================
-- § The Origin Is Always `j`-Feasible
-- ============================================================================

private def origin (q : P1.j.Params) : P1.j.Vars q := ⟨0, 0⟩

private lemma origin_feasible (q : P1.j.Params) : P1.j.Feasible q (origin q) where
  hpaper := by simpa [origin] using q.hV_nn
  hs_nn := le_refl 0
  hr_nn := le_refl 0

-- ============================================================================
-- § Disproof
-- ============================================================================

theorem aJNotReformulation :
    IsEmpty (MILPReformulation P1.a.formulation P1.j.formulation) :=
  ⟨fun Φ =>
    pEmpty_infeasible _ (Φ.bwd_feas pEmpty (origin _) (origin_feasible _))⟩

end P1
