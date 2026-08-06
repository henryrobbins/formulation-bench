import Common
import problems.p4.formulations.a.Formulation
import problems.p4.formulations.j.Formulation

/-!
# `j` is not a reformulation of `a`

Formulation `j` drops the transport and bus-limit constraints, so its origin is
feasible on every instance. Formulation `a` has an infeasible instance.
Backward feasibility therefore fails for any parameter mapping.
-/

namespace P4

private def pEmpty : P4.a.Params where
  CarCapacity := 0
  CarPollution := 0
  BusCapacity := 0
  BusPollution := 0
  MinEmployeesToTransport := 1
  MaxBuses := 0
  hCarCapacity_nn := le_refl 0
  hCarPollution_nn := le_refl 0
  hBusCapacity_nn := le_refl 0
  hBusPollution_nn := le_refl 0
  hMinEmployeesToTransport_nn := zero_le_one
  hMaxBuses_nn := le_refl 0

private lemma pEmpty_infeasible (v : P4.a.Vars pEmpty) : ¬ P4.a.Feasible pEmpty v := by
  intro h
  have := h.htransport
  norm_num [pEmpty] at this

private def origin (q : P4.j.Params) : P4.j.Vars q :=
  ⟨0, 0⟩

private lemma origin_feasible (q : P4.j.Params) : P4.j.Feasible q (origin q) where
  hm_nn := le_refl 0
  hh_nn := le_refl 0

theorem aJNotReformulation :
    IsEmpty (MILPReformulation P4.a.formulation P4.j.formulation) :=
  ⟨fun Φ => pEmpty_infeasible _
    (Φ.bwd_feas pEmpty (origin _) (origin_feasible _))⟩

end P4
