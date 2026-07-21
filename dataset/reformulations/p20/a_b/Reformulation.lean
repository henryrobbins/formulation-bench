import Common
import problems.p20.formulations.a.Formulation
import problems.p20.formulations.b.Formulation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

open BigOperators Finset

namespace P20.AB

/-!
# P20: `a → b` reformulation (rebuilt for the current formulations)

Arc-based formulation `P20.a` (cyclic node-flow) ⇄ path+cycle formulation
`P20.b`. This supersedes the old acyclic-only scaffold.

It relies on `P20.b`'s strengthened path/cycle validity: every interior node of
a path, and every node of a cycle, must be a transshipment node. That
restriction is what makes the backward map (`bwd : b → a`) land in `a`'s
feasible region — otherwise a valid path could route through a supplier and the
reconstructed flow would violate `a`'s no-supplier-inflow constraint.

The analytic heart of the `fwd` (a → b) direction is the **flow-decomposition
lemma** below: any commodity-`k` flow satisfying `a`'s structural constraints
decomposes, edge by edge, into a nonnegative combination of valid
supplier→beneficiary paths and valid transshipment cycles.

Per the user's instruction this lemma is stated and admitted with `sorry` for
now; the rest of the reformulation is meant to consume it as a black box.
Everything else in this file must remain `sorry`-free.
-/

-- ============================================================================
-- § Flow decomposition (ADMITTED — the one `sorry` in this file)
-- ============================================================================

/-- **Flow decomposition (per commodity).**

Given an `a`-feasible solution `v` and a commodity `k`, the flow `F · · k`
can be written, edge by edge, as a nonnegative combination of

* valid simple supplier→beneficiary paths (`pE q`, `pRank q`), and
* valid single transshipment cycles (`cE c`),

with path amounts `xa q ≥ 0` and cycle amounts `ya c ≥ 0`:

`F i j k = ∑_q pE q i j · xa q + ∑_c cE c i j · ya c`   for every edge `(i, j)`.

Validity is stated with `P20.b`'s (A2-strengthened) `IsValidPath` / `IsValidCycle`,
so the produced paths/cycles are exactly the ones `b` enumerates. This is the
classical flow-decomposition theorem; the constructive proof (extract a path or
a cycle from the positive support, subtract the bottleneck, recurse) is left as
future work. -/
lemma flow_decomposition
    (p : P20.a.Params) (v : P20.a.Vars p) (h : P20.a.Feasible p v) (k : Fin p.nK) :
    ∃ (nP nC : ℕ)
      (pE : Fin nP → Fin p.nN → Fin p.nN → ℤ)
      (pRank : Fin nP → Fin p.nN → ℕ)
      (cE : Fin nC → Fin p.nN → Fin p.nN → ℤ)
      (xa : Fin nP → ℝ) (ya : Fin nC → ℝ),
      (∀ q : Fin nP, P20.b.IsValidPath p.S p.T p.B p.E (pE q) (pRank q)) ∧
      (∀ c : Fin nC, P20.b.IsValidCycle p.T p.E (cE c)) ∧
      (∀ q : Fin nP, 0 ≤ xa q) ∧
      (∀ c : Fin nC, 0 ≤ ya c) ∧
      (∀ i j : Fin p.nN,
        v.F i j k
          = (∑ q : Fin nP, (pE q i j : ℝ) * xa q)
            + (∑ c : Fin nC, (cE c i j : ℝ) * ya c)) := by
  sorry

-- ============================================================================
-- § Sample consumers of `flow_decomposition`
-- ============================================================================

/-- Edge-by-edge, an `a`-feasible flow is a nonnegative combination of paths and
cycles. (Trivial repackaging of `flow_decomposition`, discarding the validity
and non-negativity data; the `fwd` map will instead keep all of it.) -/
lemma flow_is_path_cycle_combination
    (p : P20.a.Params) (v : P20.a.Vars p) (h : P20.a.Feasible p v) (k : Fin p.nK) :
    ∃ (nP nC : ℕ)
      (pE : Fin nP → Fin p.nN → Fin p.nN → ℤ)
      (cE : Fin nC → Fin p.nN → Fin p.nN → ℤ)
      (xa : Fin nP → ℝ) (ya : Fin nC → ℝ),
      ∀ i j : Fin p.nN,
        v.F i j k
          = (∑ q : Fin nP, (pE q i j : ℝ) * xa q)
            + (∑ c : Fin nC, (cE c i j : ℝ) * ya c) := by
  obtain ⟨nP, nC, pE, pRank, cE, xa, ya, _, _, _, _, hrec⟩ := flow_decomposition p v h k
  exact ⟨nP, nC, pE, cE, xa, ya, hrec⟩

/-- Ingredient for `fwd_obj`: the commodity-`k` transportation cost of an
`a`-feasible flow equals the total path/cycle shipping cost of its
decomposition, where a path's (cycle's) unit shipping cost is the sum of edge
transportation costs `∑_{i,j} tc · pE` (resp. `∑_{i,j} tc · cE`) — exactly
`b`'s `pCost` / `cCost`. -/
lemma transport_cost_decomposition
    (p : P20.a.Params) (v : P20.a.Vars p) (h : P20.a.Feasible p v) (k : Fin p.nK) :
    ∃ (nP nC : ℕ)
      (pE : Fin nP → Fin p.nN → Fin p.nN → ℤ)
      (cE : Fin nC → Fin p.nN → Fin p.nN → ℤ)
      (xa : Fin nP → ℝ) (ya : Fin nC → ℝ),
      (∀ i j : Fin p.nN,
        v.F i j k
          = (∑ q : Fin nP, (pE q i j : ℝ) * xa q)
            + (∑ c : Fin nC, (cE c i j : ℝ) * ya c)) ∧
      (∑ i : Fin p.nN, ∑ j : Fin p.nN, p.tc i j k * v.F i j k
        = (∑ q : Fin nP, xa q *
            ∑ i : Fin p.nN, ∑ j : Fin p.nN, p.tc i j k * (pE q i j : ℝ))
          + (∑ c : Fin nC, ya c *
            ∑ i : Fin p.nN, ∑ j : Fin p.nN, p.tc i j k * (cE c i j : ℝ))) := by
  obtain ⟨nP, nC, pE, pRank, cE, xa, ya, _, _, _, _, hrec⟩ := flow_decomposition p v h k
  refine ⟨nP, nC, pE, cE, xa, ya, hrec, ?_⟩
  -- Pull the path index `q` (resp. cycle index `c`) out of the edge double-sum
  -- and factor the constant amount `xa q` (resp. `ya c`).
  have hP : (∑ i : Fin p.nN, ∑ j : Fin p.nN, ∑ q : Fin nP,
              p.tc i j k * (pE q i j : ℝ) * xa q)
      = ∑ q : Fin nP, xa q *
          ∑ i : Fin p.nN, ∑ j : Fin p.nN, p.tc i j k * (pE q i j : ℝ) := by
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hC : (∑ i : Fin p.nN, ∑ j : Fin p.nN, ∑ c : Fin nC,
              p.tc i j k * (cE c i j : ℝ) * ya c)
      = ∑ c : Fin nC, ya c *
          ∑ i : Fin p.nN, ∑ j : Fin p.nN, p.tc i j k * (cE c i j : ℝ) := by
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  calc
    ∑ i : Fin p.nN, ∑ j : Fin p.nN, p.tc i j k * v.F i j k
        = ∑ i : Fin p.nN, ∑ j : Fin p.nN,
            ((∑ q : Fin nP, p.tc i j k * (pE q i j : ℝ) * xa q)
             + (∑ c : Fin nC, p.tc i j k * (cE c i j : ℝ) * ya c)) := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          rw [hrec i j, mul_add, Finset.mul_sum, Finset.mul_sum]
          congr 1
          · exact Finset.sum_congr rfl (fun q _ => by ring)
          · exact Finset.sum_congr rfl (fun c _ => by ring)
      _ = (∑ i : Fin p.nN, ∑ j : Fin p.nN, ∑ q : Fin nP,
              p.tc i j k * (pE q i j : ℝ) * xa q)
          + (∑ i : Fin p.nN, ∑ j : Fin p.nN, ∑ c : Fin nC,
              p.tc i j k * (cE c i j : ℝ) * ya c) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← Finset.sum_add_distrib]
      _ = _ := by rw [hP, hC]

-- ============================================================================
-- § Enumeration of valid paths / cycles and completeness bridges
-- ============================================================================

/-- A set of `ℤ`-indicators all of whose members are binary is finite: it embeds
into the finitely-many `Bool`-valued `nN × nN` matrices. -/
private lemma finite_binary_indicators
    {n : ℕ} (P : (Fin n → Fin n → ℤ) → Prop)
    (hbin : ∀ f, P f → ∀ i j, f i j = 0 ∨ f i j = 1) :
    {f : Fin n → Fin n → ℤ | P f}.Finite := by
  apply Set.Finite.subset
    (Set.finite_range (fun m : Fin n → Fin n → Bool => fun i j => if m i j then (1 : ℤ) else 0))
  rintro f hf
  refine ⟨fun i j => decide (f i j = 1), ?_⟩
  funext i j
  rcases hbin f hf i j with h | h <;> simp [h]

variable (pa : P20.a.Params)

/-- The valid simple supplier→beneficiary path indicators of `pa`'s graph. -/
def PathIndicatorSet : Set (Fin pa.nN → Fin pa.nN → ℤ) :=
  {pE' | ∃ pRank : Fin pa.nN → ℕ, P20.b.IsValidPath pa.S pa.T pa.B pa.E pE' pRank}

/-- The valid single-directed-cycle indicators of `pa`'s graph. -/
def CycleIndicatorSet : Set (Fin pa.nN → Fin pa.nN → ℤ) :=
  {cE' | P20.b.IsValidCycle pa.T pa.E cE'}

lemma pathIndicatorSet_finite : (PathIndicatorSet pa).Finite :=
  finite_binary_indicators _ (by rintro f ⟨pRank, hbin, -⟩; exact hbin)

lemma cycleIndicatorSet_finite : (CycleIndicatorSet pa).Finite :=
  finite_binary_indicators _ (by rintro f ⟨hbin, -⟩; exact hbin)

/-- Number of valid paths, and the enumeration of their indicators. -/
noncomputable def numPaths : ℕ := (pathIndicatorSet_finite pa).toFinset.card
noncomputable def pathEnum : Fin (numPaths pa) → (Fin pa.nN → Fin pa.nN → ℤ) :=
  fun p => ((pathIndicatorSet_finite pa).toFinset.equivFin.symm p : _)

/-- Number of valid cycles, and the enumeration of their indicators. -/
noncomputable def numCycles : ℕ := (cycleIndicatorSet_finite pa).toFinset.card
noncomputable def cycleEnum : Fin (numCycles pa) → (Fin pa.nN → Fin pa.nN → ℤ) :=
  fun c => ((cycleIndicatorSet_finite pa).toFinset.equivFin.symm c : _)

/-- **Lemma 1 — path completeness (`hpE_complete`).** Every indicator satisfying
`IsValidPath` is one of the enumerated paths. Immediate, because the
enumeration ranges over *all* valid indicators. -/
lemma pathEnum_complete
    (pE' : Fin pa.nN → Fin pa.nN → ℤ) (pRank' : Fin pa.nN → ℕ)
    (hVP : P20.b.IsValidPath pa.S pa.T pa.B pa.E pE' pRank') :
    ∃ p : Fin (numPaths pa), ∀ i j, pathEnum pa p i j = pE' i j := by
  have hmem : pE' ∈ (pathIndicatorSet_finite pa).toFinset :=
    (Set.Finite.mem_toFinset _).2 ⟨pRank', hVP⟩
  refine ⟨(pathIndicatorSet_finite pa).toFinset.equivFin ⟨pE', hmem⟩, fun i j => ?_⟩
  simp only [pathEnum, Equiv.symm_apply_apply]

/-- **Lemma 2 — cycle completeness (`hcE_complete`).** Every indicator satisfying
`IsValidCycle` is one of the enumerated cycles. -/
lemma cycleEnum_complete
    (cE' : Fin pa.nN → Fin pa.nN → ℤ)
    (hVC : P20.b.IsValidCycle pa.T pa.E cE') :
    ∃ c : Fin (numCycles pa), ∀ i j, cycleEnum pa c i j = cE' i j := by
  have hmem : cE' ∈ (cycleIndicatorSet_finite pa).toFinset :=
    (Set.Finite.mem_toFinset _).2 hVC
  refine ⟨(cycleIndicatorSet_finite pa).toFinset.equivFin ⟨cE', hmem⟩, fun i j => ?_⟩
  simp only [cycleEnum, Equiv.symm_apply_apply]

end P20.AB
