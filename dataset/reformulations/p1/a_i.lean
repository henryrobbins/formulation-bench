import Common
import problems.p1.formulations.a.Formulation
import problems.p1.formulations.i.Formulation

/-!
# `i` is not a reformulation of `a`

Formulation `i` replaces the objective by the constant `20`, so it attains at
most one objective value on any instance. Formulation `a` has instances
attaining two, and `objMap` is a bijection between the attained value sets
(`MILPReformulation.objMap_bijOn`). This holds for any parameter mapping.
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

private lemma feasible_one : P1.a.Feasible pTwo ⟨1, 0⟩ where
  hpeople := by norm_num [pTwo]
  hpaper := by norm_num [pTwo]
  hcard := zero_le_one
  hNumCashMachines_nn := zero_le_one
  hNumCardMachines_nn := le_refl 0

-- ============================================================================
-- § Disproof
-- ============================================================================

theorem aINotReformulation :
    IsEmpty (MILPReformulation P1.a.formulation P1.i.formulation) := by
  refine ⟨fun Φ => ?_⟩
  have hobj : P1.a.formulation.obj = P1.a.obj := rfl
  -- `a` attains both `0` and `1` on the witness instance.
  have hmaps := (Φ.objMap_bijOn pTwo).mapsTo
  have m0 : (0 : ℝ) ∈ P1.a.formulation.values pTwo :=
    ⟨⟨0, 0⟩, feasible_zero, by rw [hobj]; norm_num [P1.a.obj]⟩
  have m1 : (1 : ℝ) ∈ P1.a.formulation.values pTwo :=
    ⟨⟨1, 0⟩, feasible_one, by rw [hobj]; norm_num [P1.a.obj]⟩
  -- `i` attains only the constant `20`.
  have hconst : ∀ v ∈ P1.i.formulation.values (Φ.paramMap pTwo), v = 20 := by
    rintro _ ⟨x, -, rfl⟩
    rfl
  have : Φ.objMap 0 = Φ.objMap 1 :=
    (hconst _ (hmaps m0)).trans (hconst _ (hmaps m1)).symm
  exact absurd (Φ.objMap_mono.injective this) (by norm_num)

end P1
