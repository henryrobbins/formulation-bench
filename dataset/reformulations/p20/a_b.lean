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
lemma** (§ Flow decomposition, below, after the enumeration it refers to):
any `a`-feasible flow decomposes, edge by edge, into a nonnegative combination
of valid supplier→beneficiary paths and valid transshipment cycles.

Per the user's instruction that lemma is stated and admitted with `sorry` for
now; everything else in this file is `sorry`-free.
-/

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

-- ============================================================================
-- § Enumeration helpers feeding `paramMap`
-- ============================================================================

/-- Each enumerated path indicator lies in the valid-path set. -/
lemma pathEnum_mem (p : Fin (numPaths pa)) : pathEnum pa p ∈ PathIndicatorSet pa :=
  (Set.Finite.mem_toFinset _).1 ((pathIndicatorSet_finite pa).toFinset.equivFin.symm p).2

/-- Each enumerated cycle indicator lies in the valid-cycle set. -/
lemma cycleEnum_mem (c : Fin (numCycles pa)) : cycleEnum pa c ∈ CycleIndicatorSet pa :=
  (Set.Finite.mem_toFinset _).1 ((cycleIndicatorSet_finite pa).toFinset.equivFin.symm c).2

/-- Each enumerated cycle indicator is a valid cycle. -/
lemma cycleEnum_isValid (c : Fin (numCycles pa)) :
    P20.b.IsValidCycle pa.T pa.E (cycleEnum pa c) :=
  cycleEnum_mem pa c

/-- Existence of a valid rank labeling for each enumerated path. -/
lemma pathEnum_valid_ex (p : Fin (numPaths pa)) :
    ∃ pRank : Fin pa.nN → ℕ, P20.b.IsValidPath pa.S pa.T pa.B pa.E (pathEnum pa p) pRank :=
  pathEnum_mem pa p

/-- A canonical rank labeling for each enumerated path (chosen by `IsValidPath`). -/
noncomputable def pathRankOf (p : Fin (numPaths pa)) : Fin pa.nN → ℕ :=
  (pathEnum_valid_ex pa p).choose

/-- The enumerated path together with its chosen rank is a valid path. -/
lemma pathEnum_isValidPath (p : Fin (numPaths pa)) :
    P20.b.IsValidPath pa.S pa.T pa.B pa.E (pathEnum pa p) (pathRankOf pa p) :=
  (pathEnum_valid_ex pa p).choose_spec

lemma pathEnum_injective : Function.Injective (pathEnum pa) := by
  intro p₁ p₂ h
  exact (pathIndicatorSet_finite pa).toFinset.equivFin.symm.injective (Subtype.ext h)

lemma cycleEnum_injective : Function.Injective (cycleEnum pa) := by
  intro c₁ c₂ h
  exact (cycleIndicatorSet_finite pa).toFinset.equivFin.symm.injective (Subtype.ext h)

/-- Path indicators are binary. -/
lemma pathEnum_binary (p : Fin (numPaths pa)) (i j : Fin pa.nN) :
    pathEnum pa p i j = 0 ∨ pathEnum pa p i j = 1 :=
  (pathEnum_isValidPath pa p).1 i j

/-- Cycle indicators are binary. -/
lemma cycleEnum_binary (c : Fin (numCycles pa)) (i j : Fin pa.nN) :
    cycleEnum pa c i j = 0 ∨ cycleEnum pa c i j = 1 :=
  (cycleEnum_isValid pa c).1 i j

/-- Path indicators are non-negative (as reals). -/
lemma pathEnum_nonneg (p : Fin (numPaths pa)) (i j : Fin pa.nN) :
    (0 : ℝ) ≤ (pathEnum pa p i j : ℝ) := by
  rcases pathEnum_binary pa p i j with h | h <;> simp [h]

lemma cycleEnum_nonneg (c : Fin (numCycles pa)) (i j : Fin pa.nN) :
    (0 : ℝ) ≤ (cycleEnum pa c i j : ℝ) := by
  rcases cycleEnum_binary pa c i j with h | h <;> simp [h]

/-- The path-end indicator at a beneficiary is `0` or `1`: a beneficiary is
either the (unique) sink of the path or not on it — it cannot be the source,
since the source is a supplier and suppliers are disjoint from beneficiaries. -/
lemma pathEnd_binary (p : Fin (numPaths pa)) (j : Fin pa.nB) :
    (∑ i, pathEnum pa p i (pa.B j)) - (∑ k, pathEnum pa p (pa.B j) k) = 0 ∨
    (∑ i, pathEnum pa p i (pa.B j)) - (∑ k, pathEnum pa p (pa.B j) k) = 1 := by
  obtain ⟨hbin, -, hin1, hout1, hsrc, -, -, -⟩ := pathEnum_isValidPath pa p
  have hIN_nn : (0 : ℤ) ≤ ∑ i, pathEnum pa p i (pa.B j) :=
    Finset.sum_nonneg fun i _ => by rcases hbin i (pa.B j) with h | h <;> omega
  have hOUT_nn : (0 : ℤ) ≤ ∑ k, pathEnum pa p (pa.B j) k :=
    Finset.sum_nonneg fun k _ => by rcases hbin (pa.B j) k with h | h <;> omega
  have hIN_le := hin1 (pa.B j)
  have hOUT_le := hout1 (pa.B j)
  by_cases hcase :
      (∑ i, pathEnum pa p i (pa.B j)) = 0 ∧ (∑ k, pathEnum pa p (pa.B j) k) = 1
  · exfalso
    obtain ⟨s, -, -, huniq⟩ := hsrc
    exact pa.hSTB_disj_SB s j (huniq (pa.B j) ⟨hcase.2, hcase.1⟩).symm
  · omega

-- ============================================================================
-- § paramMap : a.Params → b.Params
-- ============================================================================

/-- The parameter map of the reformulation: keep `a`'s network data, take `q`
to be procurement cost `pc`, and synthesize `b`'s path/cycle structure from the
enumerations above (`pCost` / `cCost` are edge-summed transportation cost). -/
noncomputable def paramMap (pa : P20.a.Params) : P20.b.Params where
  nN := pa.nN
  nS := pa.nS
  nT := pa.nT
  nB := pa.nB
  nP := numPaths pa
  nC := numCycles pa
  nK := pa.nK
  nL := pa.nL
  S := pa.S
  T := pa.T
  B := pa.B
  E := pa.E
  pE := pathEnum pa
  pRank := pathRankOf pa
  pCost := fun p k => ∑ i, ∑ j, pa.tc i j k * (pathEnum pa p i j : ℝ)
  cE := cycleEnum pa
  cCost := fun c k => ∑ i, ∑ j, pa.tc i j k * (cycleEnum pa c i j : ℝ)
  q := pa.pc
  nutval := pa.nutval
  nutreq := pa.nutreq
  dem := pa.dem
  e := fun j p => (∑ i, pathEnum pa p i (pa.B j)) - (∑ k, pathEnum pa p (pa.B j) k)
  hE_bin := pa.hE_bin
  he_bin := fun j p => pathEnd_binary pa p j
  hSTB_partition := pa.hSTB_partition
  hSTB_disj_ST := pa.hSTB_disj_ST
  hSTB_disj_SB := pa.hSTB_disj_SB
  hSTB_disj_TB := pa.hSTB_disj_TB
  hS_inj := pa.hS_inj
  hT_inj := pa.hT_inj
  hB_inj := pa.hB_inj
  hnN := pa.hnN
  hnS := pa.hnS
  hnT := pa.hnT
  hnB := pa.hnB
  hnK := pa.hnK
  hnL := pa.hnL
  hpCost_nn := fun p k => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (pa.htc_nn i j k) (pathEnum_nonneg pa p i j)
  hcCost_nn := fun c k => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (pa.htc_nn i j k) (cycleEnum_nonneg pa c i j)
  hq_nn := pa.hpc_nn
  hnutval_nn := pa.hnutval_nn
  hnutreq_nn := pa.hnutreq_nn
  hdem_nn := pa.hdem_nn
  hpE_valid := pathEnum_isValidPath pa
  hpE_endE := fun _ _ => rfl
  hpE_complete := fun pE' pRank' h => pathEnum_complete pa pE' pRank' h
  hpE_inj := fun _ _ h => pathEnum_injective pa (funext fun i => funext fun j => h i j)
  hcE_valid := cycleEnum_isValid pa
  hcE_complete := fun cE' h => cycleEnum_complete pa cE' h
  hcE_inj := fun _ _ h => cycleEnum_injective pa (funext fun i => funext fun j => h i j)

-- ============================================================================
-- § Flow decomposition (ADMITTED — the one `sorry`) and the fwd / bwd maps
-- ============================================================================

/-- **Flow decomposition (fixed-index form).** Any `a`-feasible flow decomposes,
edge by edge and for every commodity, into a nonnegative combination of the
enumerated paths and cycles:
`F i j k = ∑_p pathEnum p i j · x p k + ∑_c cycleEnum c i j · y c k`.
This is the classical flow-decomposition theorem (extract a path or a cycle from
the positive support, subtract the bottleneck, recurse); admitted for now. The
fixed-index phrasing (amounts indexed by the reformulation's own `numPaths` /
`numCycles`) is what lets `fwd` consume it without a separate re-indexing step. -/
lemma flow_decomposition (v : P20.a.Vars pa) (h : P20.a.Feasible pa v) :
    ∃ (x : Fin (numPaths pa) → Fin pa.nK → ℝ) (y : Fin (numCycles pa) → Fin pa.nK → ℝ),
      (∀ p k, 0 ≤ x p k) ∧ (∀ c k, 0 ≤ y c k) ∧
      (∀ i j : Fin pa.nN, ∀ k : Fin pa.nK,
        v.F i j k
          = (∑ p, (pathEnum pa p i j : ℝ) * x p k)
            + (∑ c, (cycleEnum pa c i j : ℝ) * y c k)) := by
  sorry

/-- Forward map (a → b): decompose the flow into path/cycle amounts, keep `R`.
Total on all of `a.Vars`; the decomposition is used only in the feasible case. -/
noncomputable def fwd (v : P20.a.Vars pa) : P20.b.Vars (paramMap pa) := by
  classical
  exact
    if h : P20.a.Feasible pa v then
      { x := (flow_decomposition pa v h).choose
        y := (flow_decomposition pa v h).choose_spec.choose
        R := v.R }
    else
      { x := fun _ _ => 0
        y := fun _ _ => 0
        R := v.R }

/-- Backward map (b → a): rebuild the arc flow by summing the path and cycle
contributions on each edge, keep `R`. -/
noncomputable def bwd (vb : P20.b.Vars (paramMap pa)) : P20.a.Vars pa where
  F := fun i j k =>
    (∑ p, (pathEnum pa p i j : ℝ) * vb.x p k)
      + (∑ c, (cycleEnum pa c i j : ℝ) * vb.y c k)
  R := vb.R

/-- In the feasible case, `fwd`'s components are exactly a valid flow
decomposition: non-negative and reconstructing `v.F`. This is the handle the
`fwd` feasibility/objective proofs will use. -/
lemma fwd_spec (v : P20.a.Vars pa) (h : P20.a.Feasible pa v) :
    (∀ p k, 0 ≤ (fwd pa v).x p k) ∧ (∀ c k, 0 ≤ (fwd pa v).y c k) ∧
    (∀ i j : Fin pa.nN, ∀ k : Fin pa.nK,
      v.F i j k
        = (∑ p, (pathEnum pa p i j : ℝ) * (fwd pa v).x p k)
          + (∑ c, (cycleEnum pa c i j : ℝ) * (fwd pa v).y c k)) := by
  have hx : (fwd pa v).x = (flow_decomposition pa v h).choose := by
    simp only [fwd, dif_pos h]
  have hy : (fwd pa v).y = (flow_decomposition pa v h).choose_spec.choose := by
    simp only [fwd, dif_pos h]
  rw [hx, hy]
  exact (flow_decomposition pa v h).choose_spec.choose_spec

/-- `fwd` and `bwd` both keep the ration `R` unchanged. -/
@[simp] lemma bwd_R (vb : P20.b.Vars (paramMap pa)) : (bwd pa vb).R = vb.R := rfl

-- ============================================================================
-- § Node-class flow facts for enumerated paths / cycles (feed `bwd_feas`)
-- ============================================================================

/-- A valid path has zero in-degree at a supplier (it can only be the source). -/
lemma path_supplier_indeg_zero (p : Fin (numPaths pa)) (s : Fin pa.nS) :
    ∑ i, pathEnum pa p i (pa.S s) = 0 := by
  obtain ⟨hbin, -, hin1, hout1, -, hsink, hinterior, -⟩ := pathEnum_isValidPath pa p
  set IN := ∑ i, pathEnum pa p i (pa.S s)
  set OUT := ∑ j, pathEnum pa p (pa.S s) j
  have hIN_nn : 0 ≤ IN := Finset.sum_nonneg fun i _ => by
    rcases hbin i (pa.S s) with h | h <;> omega
  have hIN_le : IN ≤ 1 := hin1 (pa.S s)
  have hOUT_nn : 0 ≤ OUT := Finset.sum_nonneg fun j _ => by
    rcases hbin (pa.S s) j with h | h <;> omega
  have hOUT_le : OUT ≤ 1 := hout1 (pa.S s)
  by_contra hne
  have hIN1 : IN = 1 := by omega
  rcases (show OUT = 0 ∨ OUT = 1 by omega) with hO | hO
  · obtain ⟨b, -, -, hbuniq⟩ := hsink
    exact pa.hSTB_disj_SB s b (hbuniq (pa.S s) ⟨hIN1, hO⟩)
  · obtain ⟨t, ht⟩ := hinterior (pa.S s) hIN1 hO
    exact pa.hSTB_disj_ST s t ht.symm

/-- A valid path has zero out-degree at a beneficiary (it can only be the sink). -/
lemma path_beneficiary_outdeg_zero (p : Fin (numPaths pa)) (b : Fin pa.nB) :
    ∑ j, pathEnum pa p (pa.B b) j = 0 := by
  obtain ⟨hbin, -, hin1, hout1, hsrc, -, hinterior, -⟩ := pathEnum_isValidPath pa p
  set IN := ∑ i, pathEnum pa p i (pa.B b)
  set OUT := ∑ j, pathEnum pa p (pa.B b) j
  have hIN_nn : 0 ≤ IN := Finset.sum_nonneg fun i _ => by
    rcases hbin i (pa.B b) with h | h <;> omega
  have hIN_le : IN ≤ 1 := hin1 (pa.B b)
  have hOUT_nn : 0 ≤ OUT := Finset.sum_nonneg fun j _ => by
    rcases hbin (pa.B b) j with h | h <;> omega
  have hOUT_le : OUT ≤ 1 := hout1 (pa.B b)
  by_contra hne
  have hOUT1 : OUT = 1 := by omega
  rcases (show IN = 0 ∨ IN = 1 by omega) with hI | hI
  · obtain ⟨s, -, -, hsuniq⟩ := hsrc
    exact pa.hSTB_disj_SB s b (hsuniq (pa.B b) ⟨hOUT1, hI⟩).symm
  · obtain ⟨t, ht⟩ := hinterior (pa.B b) hI hOUT1
    exact pa.hSTB_disj_TB t b ht

/-- A valid path has equal in- and out-degree at a transshipment node. -/
lemma path_transshipment_deg (p : Fin (numPaths pa)) (t : Fin pa.nT) :
    ∑ i, pathEnum pa p i (pa.T t) = ∑ j, pathEnum pa p (pa.T t) j := by
  obtain ⟨hbin, -, hin1, hout1, hsrc, hsink, -, -⟩ := pathEnum_isValidPath pa p
  set IN := ∑ i, pathEnum pa p i (pa.T t)
  set OUT := ∑ j, pathEnum pa p (pa.T t) j
  have hIN_nn : 0 ≤ IN := Finset.sum_nonneg fun i _ => by
    rcases hbin i (pa.T t) with h | h <;> omega
  have hIN_le : IN ≤ 1 := hin1 (pa.T t)
  have hOUT_nn : 0 ≤ OUT := Finset.sum_nonneg fun j _ => by
    rcases hbin (pa.T t) j with h | h <;> omega
  have hOUT_le : OUT ≤ 1 := hout1 (pa.T t)
  by_contra hne
  rcases (show (IN = 0 ∧ OUT = 1) ∨ (IN = 1 ∧ OUT = 0) by omega) with ⟨hI, hO⟩ | ⟨hI, hO⟩
  · obtain ⟨s, -, -, hsuniq⟩ := hsrc
    exact pa.hSTB_disj_ST s t (hsuniq (pa.T t) ⟨hO, hI⟩).symm
  · obtain ⟨b, -, -, hbuniq⟩ := hsink
    exact pa.hSTB_disj_TB t b (hbuniq (pa.T t) ⟨hI, hO⟩)

/-- A valid cycle has zero out-degree at a supplier (its nodes are transshipment). -/
lemma cycle_supplier_deg_zero (c : Fin (numCycles pa)) (s : Fin pa.nS) :
    ∑ i, cycleEnum pa c i (pa.S s) = 0 := by
  obtain ⟨hbin, -, -, hout1, hcons, htrans, -⟩ := cycleEnum_isValid pa c
  have hOUT_nn : 0 ≤ ∑ j, cycleEnum pa c (pa.S s) j := Finset.sum_nonneg fun j _ => by
    rcases hbin (pa.S s) j with h | h <;> omega
  have hOUT_le : ∑ j, cycleEnum pa c (pa.S s) j ≤ 1 := hout1 (pa.S s)
  have hout0 : ∑ j, cycleEnum pa c (pa.S s) j = 0 := by
    by_contra hne
    have h1 : ∑ j, cycleEnum pa c (pa.S s) j = 1 := by omega
    obtain ⟨t, ht⟩ := htrans (pa.S s) h1
    exact pa.hSTB_disj_ST s t ht.symm
  rw [hcons (pa.S s)]; exact hout0

/-- A valid cycle has zero out-degree at a beneficiary. -/
lemma cycle_beneficiary_outdeg_zero (c : Fin (numCycles pa)) (b : Fin pa.nB) :
    ∑ j, cycleEnum pa c (pa.B b) j = 0 := by
  obtain ⟨hbin, -, -, hout1, -, htrans, -⟩ := cycleEnum_isValid pa c
  have hnn : 0 ≤ ∑ j, cycleEnum pa c (pa.B b) j := Finset.sum_nonneg fun j _ => by
    rcases hbin (pa.B b) j with h | h <;> omega
  have hle : ∑ j, cycleEnum pa c (pa.B b) j ≤ 1 := hout1 (pa.B b)
  by_contra hne
  have h1 : ∑ j, cycleEnum pa c (pa.B b) j = 1 := by omega
  obtain ⟨t, ht⟩ := htrans (pa.B b) h1
  exact pa.hSTB_disj_TB t b ht

/-- Pointwise consequence: a valid path carries no edge into a supplier. -/
lemma path_supplier_no_inflow (p : Fin (numPaths pa)) (s : Fin pa.nS) (i : Fin pa.nN) :
    pathEnum pa p i (pa.S s) = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun i' _ => by
    rcases pathEnum_binary pa p i' (pa.S s) with h | h <;> omega)).1
    (path_supplier_indeg_zero pa p s) i (Finset.mem_univ i)

lemma path_beneficiary_no_outflow (p : Fin (numPaths pa)) (b : Fin pa.nB) (j : Fin pa.nN) :
    pathEnum pa p (pa.B b) j = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun j' _ => by
    rcases pathEnum_binary pa p (pa.B b) j' with h | h <;> omega)).1
    (path_beneficiary_outdeg_zero pa p b) j (Finset.mem_univ j)

lemma cycle_supplier_no_inflow (c : Fin (numCycles pa)) (s : Fin pa.nS) (i : Fin pa.nN) :
    cycleEnum pa c i (pa.S s) = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun i' _ => by
    rcases cycleEnum_binary pa c i' (pa.S s) with h | h <;> omega)).1
    (cycle_supplier_deg_zero pa c s) i (Finset.mem_univ i)

lemma cycle_beneficiary_no_outflow (c : Fin (numCycles pa)) (b : Fin pa.nB) (j : Fin pa.nN) :
    cycleEnum pa c (pa.B b) j = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun j' _ => by
    rcases cycleEnum_binary pa c (pa.B b) j' with h | h <;> omega)).1
    (cycle_beneficiary_outdeg_zero pa c b) j (Finset.mem_univ j)

-- ============================================================================
-- § bwd_feas : b-feasible ⟹ a-feasible
-- ============================================================================

/-- Off a graph edge, the reconstructed flow vanishes (paths/cycles are subgraphs). -/
lemma bwd_F_zero_offedge (vb : P20.b.Vars (paramMap pa)) (i j : Fin pa.nN) (k : Fin pa.nK)
    (hE : pa.E i j = 0) : (bwd pa vb).F i j k = 0 := by
  have hpz : ∀ p, (pathEnum pa p i j : ℝ) = 0 := by
    intro p
    have hle := (pathEnum_isValidPath pa p).2.1 i j
    rcases pathEnum_binary pa p i j with h | h
    · simp [h]
    · exfalso; rw [h, hE] at hle; omega
  have hcz : ∀ c, (cycleEnum pa c i j : ℝ) = 0 := by
    intro c
    have hle := (cycleEnum_isValid pa c).2.1 i j
    rcases cycleEnum_binary pa c i j with h | h
    · simp [h]
    · exfalso; rw [h, hE] at hle; omega
  show (∑ p, (pathEnum pa p i j : ℝ) * vb.x p k) + (∑ c, (cycleEnum pa c i j : ℝ) * vb.y c k) = 0
  have h1 : (∑ p, (pathEnum pa p i j : ℝ) * vb.x p k) = 0 :=
    Finset.sum_eq_zero fun p _ => by rw [hpz p]; ring
  have h2 : (∑ c, (cycleEnum pa c i j : ℝ) * vb.y c k) = 0 :=
    Finset.sum_eq_zero fun c _ => by rw [hcz c]; ring
  rw [h1, h2, add_zero]

/-- The graph-edge indicator is redundant against the reconstructed flow. -/
lemma bwd_E_mul (vb : P20.b.Vars (paramMap pa)) (i j : Fin pa.nN) (k : Fin pa.nK) :
    (pa.E i j : ℝ) * (bwd pa vb).F i j k = (bwd pa vb).F i j k := by
  rcases pa.hE_bin i j with h | h
  · rw [bwd_F_zero_offedge pa vb i j k h]; ring
  · rw [h]; simp

/-- Total in-flow at a node is the path/cycle in-degrees weighted by amounts. -/
lemma sum_bwd_F_in (vb : P20.b.Vars (paramMap pa)) (w : Fin pa.nN) (k : Fin pa.nK) :
    ∑ i, (bwd pa vb).F i w k
      = (∑ p, (↑(∑ i, pathEnum pa p i w) : ℝ) * vb.x p k)
        + (∑ c, (↑(∑ i, cycleEnum pa c i w) : ℝ) * vb.y c k) := by
  simp only [bwd]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_mul]; push_cast; ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_mul]; push_cast; ring

/-- Total out-flow at a node is the path/cycle out-degrees weighted by amounts. -/
lemma sum_bwd_F_out (vb : P20.b.Vars (paramMap pa)) (w : Fin pa.nN) (k : Fin pa.nK) :
    ∑ i, (bwd pa vb).F w i k
      = (∑ p, (↑(∑ i, pathEnum pa p w i) : ℝ) * vb.x p k)
        + (∑ c, (↑(∑ i, cycleEnum pa c w i) : ℝ) * vb.y c k) := by
  simp only [bwd]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_mul]; push_cast; ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_mul]; push_cast; ring

/-- **Backward feasibility.** A `b`-feasible solution maps to an `a`-feasible one. -/
lemma bwd_feas (vb : P20.b.Vars (paramMap pa)) (hb : P20.b.Feasible (paramMap pa) vb) :
    P20.a.Feasible pa (bwd pa vb) where
  hS_noinflow := fun s k => by
    have hFz : ∀ i, (bwd pa vb).F i (pa.S s) k = 0 := fun i => by
      show (∑ p, (pathEnum pa p i (pa.S s) : ℝ) * vb.x p k)
            + (∑ c, (cycleEnum pa c i (pa.S s) : ℝ) * vb.y c k) = 0
      have h1 : (∑ p, (pathEnum pa p i (pa.S s) : ℝ) * vb.x p k) = 0 :=
        Finset.sum_eq_zero fun p _ => by simp [path_supplier_no_inflow pa p s i]
      have h2 : (∑ c, (cycleEnum pa c i (pa.S s) : ℝ) * vb.y c k) = 0 :=
        Finset.sum_eq_zero fun c _ => by simp [cycle_supplier_no_inflow pa c s i]
      rw [h1, h2, add_zero]
    apply Finset.sum_eq_zero
    intro i _; rw [hFz i]; ring
  hflow := fun t k => by
    rw [Finset.sum_congr rfl (fun i _ => bwd_E_mul pa vb i (pa.T t) k),
        Finset.sum_congr rfl (fun i _ => bwd_E_mul pa vb (pa.T t) i k),
        sum_bwd_F_in pa vb (pa.T t) k, sum_bwd_F_out pa vb (pa.T t) k]
    congr 1
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [path_transshipment_deg pa p t]
    · refine Finset.sum_congr rfl fun c _ => ?_
      obtain ⟨-, -, -, -, hcons, -, -⟩ := cycleEnum_isValid pa c
      rw [hcons (pa.T t)]
  hB_nooutflow := fun b k => by
    have hFz : ∀ j, (bwd pa vb).F (pa.B b) j k = 0 := fun j => by
      show (∑ p, (pathEnum pa p (pa.B b) j : ℝ) * vb.x p k)
            + (∑ c, (cycleEnum pa c (pa.B b) j : ℝ) * vb.y c k) = 0
      have h1 : (∑ p, (pathEnum pa p (pa.B b) j : ℝ) * vb.x p k) = 0 :=
        Finset.sum_eq_zero fun p _ => by simp [path_beneficiary_no_outflow pa p b j]
      have h2 : (∑ c, (cycleEnum pa c (pa.B b) j : ℝ) * vb.y c k) = 0 :=
        Finset.sum_eq_zero fun c _ => by simp [cycle_beneficiary_no_outflow pa c b j]
      rw [h1, h2, add_zero]
    apply Finset.sum_eq_zero
    intro j _; rw [hFz j]; ring
  hdemand := fun j k => by
    rw [Finset.sum_congr rfl (fun i _ => bwd_E_mul pa vb i (pa.B j) k),
        sum_bwd_F_in pa vb (pa.B j) k]
    have hcyc0 : (∑ c, (↑(∑ i, cycleEnum pa c i (pa.B j)) : ℝ) * vb.y c k) = 0 := by
      apply Finset.sum_eq_zero; intro c _
      obtain ⟨-, -, -, -, hcons, -, -⟩ := cycleEnum_isValid pa c
      rw [hcons (pa.B j), cycle_beneficiary_outdeg_zero pa c j]; simp
    rw [hcyc0, add_zero]
    have hep : (∑ p, (↑(∑ i, pathEnum pa p i (pa.B j)) : ℝ) * vb.x p k)
        = ∑ p, ((paramMap pa).e j p : ℝ) * vb.x p k := by
      apply Finset.sum_congr rfl; intro p _
      have he : (paramMap pa).e j p = ∑ i, pathEnum pa p i (pa.B j) := by
        show (∑ i, pathEnum pa p i (pa.B j)) - (∑ k, pathEnum pa p (pa.B j) k)
              = ∑ i, pathEnum pa p i (pa.B j)
        rw [path_beneficiary_outdeg_zero pa p j]; ring
      rw [he]
    rw [hep]
    exact hb.hdemand j k
  hnutrition := fun l => hb.hnutrition l
  hF_offedge := fun i j k hE => bwd_F_zero_offedge pa vb i j k hE
  hF_nn := fun i j k => by
    show 0 ≤ (∑ p, (pathEnum pa p i j : ℝ) * vb.x p k)
          + (∑ c, (cycleEnum pa c i j : ℝ) * vb.y c k)
    exact add_nonneg
      (Finset.sum_nonneg fun p _ => mul_nonneg (pathEnum_nonneg pa p i j) (hb.hx_nn p k))
      (Finset.sum_nonneg fun c _ => mul_nonneg (cycleEnum_nonneg pa c i j) (hb.hy_nn c k))
  hR_nn := fun k => hb.hR_nn k

end P20.AB
