import Common
import problems.p20.formulations.a.Formulation
import problems.p20.formulations.b.Formulation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

/-!
# P20: `a → b` reformulation (rebuilt for the current formulations)

Arc-based formulation `P20.a` (cyclic node-flow) ⇄ path+cycle formulation
`P20.b`. This supersedes the old acyclic-only scaffold.

It relies on the graph assumptions that suppliers have no incoming arcs and
beneficiary camps have no outgoing arcs. Together with path/cycle edge support,
these assumptions imply the node-class restrictions needed by the forward and
backward maps.

The analytic heart of the `fwd` (a → b) direction is the **flow-decomposition
lemma** below: any commodity-`k` flow satisfying `a`'s structural constraints
decomposes, edge by edge, into a nonnegative combination of valid
supplier→beneficiary paths and valid transshipment cycles.

The proof below formalizes the classical finite-support argument: extract a
simple positive path or cycle, subtract its bottleneck flow, and recurse on the
strictly smaller positive support.
-/

open BigOperators Finset

namespace P20.AB

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

/-- A finite-support subtraction argument: if every nonzero member of `Good`
contains a nonempty binary atom in its positive support, and subtracting an
atom preserves `Good`, then every nonnegative member of `Good` is a
nonnegative conic combination of the atoms. -/
private lemma finite_conic_decomposition
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (atom : α → ι → ℝ) (Good : (ι → ℝ) → Prop)
    (hextract : ∀ f : ι → ℝ, Good f → (∀ i, 0 ≤ f i) →
      (∃ i, 0 < f i) →
      ∃ a : α,
        (∀ i, atom a i = 0 ∨ atom a i = 1) ∧
        (∃ i, atom a i = 1) ∧
        (∀ i, atom a i = 1 → 0 < f i))
    (hsub : ∀ (f : ι → ℝ) (a : α) (d : ℝ), Good f →
      Good (fun i => f i - d * atom a i)) :
    ∀ f : ι → ℝ, Good f → (∀ i, 0 ≤ f i) →
      ∃ z : α → ℝ, (∀ a, 0 ≤ z a) ∧
        ∀ i, f i = ∑ a, atom a i * z a := by
  classical
  intro f
  let suppCard (g : ι → ℝ) : ℕ := (Finset.univ.filter fun i => 0 < g i).card
  induction hs : suppCard f using Nat.strong_induction_on generalizing f with
  | h n ih =>
      intro hf hnn
      by_cases hpos : ∃ i, 0 < f i
      · obtain ⟨a, habin, ha_ne, ha_support⟩ := hextract f hf hnn hpos
        let active : Finset ι := Finset.univ.filter fun i => atom a i = 1
        have hactive : active.Nonempty := by
          rcases ha_ne with ⟨i, hi⟩
          exact ⟨i, by simp [active, hi]⟩
        let values : Finset ℝ := active.image f
        have hvalues : values.Nonempty := hactive.image f
        let d : ℝ := values.min' hvalues
        have hd_pos : 0 < d := by
          have hdmem : d ∈ values := values.min'_mem hvalues
          obtain ⟨i, hi, hid⟩ := Finset.mem_image.mp hdmem
          rw [← hid]
          exact ha_support i (by simpa [active] using hi)
        have hd_le (i : ι) (hi : atom a i = 1) : d ≤ f i := by
          apply values.min'_le
          exact Finset.mem_image.mpr ⟨i, by simp [active, hi], rfl⟩
        let g : ι → ℝ := fun i => f i - d * atom a i
        have hgnn : ∀ i, 0 ≤ g i := by
          intro i
          rcases habin i with hi | hi
          · simp [g, hi, hnn i]
          · simp [g, hi, hd_le i hi]
        have hg : Good g := hsub f a d hf
        have hsupp_subset :
            (Finset.univ.filter fun i => 0 < g i) ⊆
              (Finset.univ.filter fun i => 0 < f i) := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          rcases habin i with hai | hai
          · simpa [g, hai] using hi
          · have := hi
            simp only [g, hai, mul_one] at this
            linarith
        have hsupp_ssubset :
            (Finset.univ.filter fun i => 0 < g i) ⊂
              (Finset.univ.filter fun i => 0 < f i) := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨hsupp_subset, ?_⟩
          have hdmem : d ∈ values := values.min'_mem hvalues
          obtain ⟨i, hi, hfi⟩ := Finset.mem_image.mp hdmem
          have hai : atom a i = 1 := by simpa [active] using hi
          have hfi : f i = d := hfi
          intro heq
          have himem_f : i ∈ Finset.univ.filter fun i => 0 < f i := by
            simp [hfi, hd_pos]
          have himem_g : i ∈ Finset.univ.filter fun i => 0 < g i := heq ▸ himem_f
          simp [g, hai, hfi] at himem_g
        have hcard_lt : suppCard g < n := by
          rw [← hs]
          exact Finset.card_lt_card hsupp_ssubset
        obtain ⟨z, hz_nn, hz⟩ := ih (suppCard g) hcard_lt g rfl hg hgnn
        refine ⟨fun b => z b + if b = a then d else 0, ?_, ?_⟩
        · intro b
          by_cases hba : b = a
          · subst b
            simpa using add_nonneg (hz_nn a) (le_of_lt hd_pos)
          · simp [hba, hz_nn b]
        · intro i
          rw [show f i = g i + d * atom a i by simp [g]]
          rw [hz i]
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
          simp
          ring
      · refine ⟨fun _ => 0, fun _ => le_rfl, ?_⟩
        intro i
        have hfi : f i = 0 := le_antisymm (not_lt.mp fun hi => hpos ⟨i, hi⟩) (hnn i)
        simp [hfi]

variable (pa : P20.a.Params)

/-- The valid simple supplier→beneficiary path indicators of `pa`'s graph. -/
def PathIndicatorSet : Set (Fin pa.nN → Fin pa.nN → ℤ) :=
  {pE' | ∃ pRank : Fin pa.nN → ℕ, P20.b.IsValidPath pa.S pa.B pa.E pE' pRank}

/-- The valid single-directed-cycle indicators of `pa`'s graph. -/
def CycleIndicatorSet : Set (Fin pa.nN → Fin pa.nN → ℤ) :=
  {cE' | P20.b.IsValidCycle pa.E cE'}

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
    (hVP : P20.b.IsValidPath pa.S pa.B pa.E pE' pRank') :
    ∃ p : Fin (numPaths pa), ∀ i j, pathEnum pa p i j = pE' i j := by
  have hmem : pE' ∈ (pathIndicatorSet_finite pa).toFinset :=
    (Set.Finite.mem_toFinset _).2 ⟨pRank', hVP⟩
  refine ⟨(pathIndicatorSet_finite pa).toFinset.equivFin ⟨pE', hmem⟩, fun i j => ?_⟩
  simp only [pathEnum, Equiv.symm_apply_apply]

/-- **Lemma 2 — cycle completeness (`hcE_complete`).** Every indicator satisfying
`IsValidCycle` is one of the enumerated cycles. -/
lemma cycleEnum_complete
    (cE' : Fin pa.nN → Fin pa.nN → ℤ)
    (hVC : P20.b.IsValidCycle pa.E cE') :
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
    P20.b.IsValidCycle pa.E (cycleEnum pa c) :=
  cycleEnum_mem pa c

/-- Existence of a valid rank labeling for each enumerated path. -/
lemma pathEnum_valid_ex (p : Fin (numPaths pa)) :
    ∃ pRank : Fin pa.nN → ℕ, P20.b.IsValidPath pa.S pa.B pa.E (pathEnum pa p) pRank :=
  pathEnum_mem pa p

/-- A canonical rank labeling for each enumerated path (chosen by `IsValidPath`). -/
noncomputable def pathRankOf (p : Fin (numPaths pa)) : Fin pa.nN → ℕ :=
  (pathEnum_valid_ex pa p).choose

/-- The enumerated path together with its chosen rank is a valid path. -/
lemma pathEnum_isValidPath (p : Fin (numPaths pa)) :
    P20.b.IsValidPath pa.S pa.B pa.E (pathEnum pa p) (pathRankOf pa p) :=
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

private lemma pathEnum_zero_of_E_zero (p : Fin (numPaths pa)) (i j : Fin pa.nN)
    (hE : pa.E i j = 0) : pathEnum pa p i j = 0 := by
  obtain ⟨hbin, hsub, -⟩ := pathEnum_isValidPath pa p
  have hle := hsub i j
  rcases hbin i j with h | h
  · exact h
  · omega

private lemma cycleEnum_zero_of_E_zero (c : Fin (numCycles pa)) (i j : Fin pa.nN)
    (hE : pa.E i j = 0) : cycleEnum pa c i j = 0 := by
  obtain ⟨hbin, hsub, -⟩ := cycleEnum_isValid pa c
  have hle := hsub i j
  rcases hbin i j with h | h
  · exact h
  · omega

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
  obtain ⟨hbin, -, hin1, hout1, hsrc, -, -⟩ := pathEnum_isValidPath pa p
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
  hE_noinflow_S := pa.hE_noinflow_S
  hE_nooutflow_B := pa.hE_nooutflow_B
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
-- § Simple-list indicators
-- ============================================================================

/-- `(u,w)` occurs as a consecutive pair in `L`. -/
private def Consec {α : Type*} (L : List α) (u w : α) : Prop :=
  ∃ pre suf : List α, L = pre ++ u :: w :: suf

private lemma consec_left_mem {α : Type*} {L : List α} {u w : α}
    (h : Consec L u w) : u ∈ L := by
  obtain ⟨pre, suf, rfl⟩ := h
  simp

private lemma consec_right_mem {α : Type*} {L : List α} {u w : α}
    (h : Consec L u w) : w ∈ L := by
  obtain ⟨pre, suf, rfl⟩ := h
  simp

private lemma consec_chain {α : Type*} {R : α → α → Prop} {L : List α} {u w : α}
    (hch : L.IsChain R) (h : Consec L u w) : R u w := by
  obtain ⟨pre, suf, rfl⟩ := h
  rw [List.isChain_append] at hch
  rcases hch with ⟨_, hch2, _⟩
  rw [List.isChain_cons_cons] at hch2
  exact hch2.1

private lemma getElem?_consec_left {α : Type*} (pre suf : List α) (u w : α) :
    (pre ++ u :: w :: suf)[pre.length]? = some u := by
  have hL : pre ++ u :: w :: suf = pre ++ [u] ++ (w :: suf) := by simp
  rw [hL, List.getElem?_append_left (by simp), List.getElem?_append_right (by simp)]
  simp

private lemma getElem?_consec_right {α : Type*} (pre suf : List α) (u w : α) :
    (pre ++ u :: w :: suf)[pre.length + 1]? = some w := by
  have hL : pre ++ u :: w :: suf = (pre ++ [u]) ++ (w :: suf) := by simp
  rw [hL, List.getElem?_append_right (by simp)]
  simp

private lemma getElem?_eq_some_iff_unique_of_nodup {α : Type*} {L : List α}
    (hnd : L.Nodup) {u : α} {n : ℕ}
    (hn : L[n]? = some u) {m : ℕ} (hm : L[m]? = some u) : n = m := by
  by_contra hne
  rw [List.getElem?_eq_some_iff] at hn hm
  obtain ⟨hnL, h1⟩ := hn
  obtain ⟨hmL, h2⟩ := hm
  exact hne (List.Nodup.getElem_inj_iff hnd |>.mp (h1.trans h2.symm))

private lemma consec_pred_unique {α : Type*} {L : List α} (hnd : L.Nodup)
    {u₁ u₂ w : α} (h₁ : Consec L u₁ w) (h₂ : Consec L u₂ w) : u₁ = u₂ := by
  obtain ⟨p₁, s₁, hL₁⟩ := h₁
  obtain ⟨p₂, s₂, hL₂⟩ := h₂
  have hw1 : L[p₁.length + 1]? = some w := by
    rw [hL₁]
    exact getElem?_consec_right _ _ _ _
  have hw2 : L[p₂.length + 1]? = some w := by
    rw [hL₂]
    exact getElem?_consec_right _ _ _ _
  have heq : p₁.length + 1 = p₂.length + 1 :=
    getElem?_eq_some_iff_unique_of_nodup hnd hw1 hw2
  have hpeq : p₁.length = p₂.length := by omega
  have hu1 : L[p₁.length]? = some u₁ := by
    rw [hL₁]
    exact getElem?_consec_left _ _ _ _
  have hu2 : L[p₂.length]? = some u₂ := by
    rw [hL₂]
    exact getElem?_consec_left _ _ _ _
  rw [hpeq] at hu1
  rw [hu1] at hu2
  exact Option.some.inj hu2

private lemma consec_succ_unique {α : Type*} {L : List α} (hnd : L.Nodup)
    {u w₁ w₂ : α} (h₁ : Consec L u w₁) (h₂ : Consec L u w₂) : w₁ = w₂ := by
  obtain ⟨p₁, s₁, hL₁⟩ := h₁
  obtain ⟨p₂, s₂, hL₂⟩ := h₂
  have hu1 : L[p₁.length]? = some u := by
    rw [hL₁]
    exact getElem?_consec_left _ _ _ _
  have hu2 : L[p₂.length]? = some u := by
    rw [hL₂]
    exact getElem?_consec_left _ _ _ _
  have hpeq : p₁.length = p₂.length :=
    getElem?_eq_some_iff_unique_of_nodup hnd hu1 hu2
  have hw1 : L[p₁.length + 1]? = some w₁ := by
    rw [hL₁]
    exact getElem?_consec_right _ _ _ _
  have hw2 : L[p₂.length + 1]? = some w₂ := by
    rw [hL₂]
    exact getElem?_consec_right _ _ _ _
  rw [hpeq] at hw1
  rw [hw1] at hw2
  exact Option.some.inj hw2

private lemma consec_no_pred_head {α : Type*} {a : α} {as : List α}
    (hnd : (a :: as).Nodup) : ∀ u, ¬ Consec (a :: as) u a := by
  intro u ⟨pre, suf, hL⟩
  have h0 : (a :: as)[0]? = some a := by simp
  have h1 : (a :: as)[pre.length + 1]? = some a := by
    rw [hL]
    exact getElem?_consec_right _ _ _ _
  have heq : 0 = pre.length + 1 :=
    getElem?_eq_some_iff_unique_of_nodup hnd h0 h1
  omega

private lemma consec_no_succ_last {α : Type*} {L : List α} (hne : L ≠ [])
    (hnd : L.Nodup) : ∀ w, ¬ Consec L (L.getLast hne) w := by
  intro w ⟨pre, suf, hL⟩
  set u := L.getLast hne with hu_def
  have h_last : L[L.length - 1]? = some u := by
    rw [hu_def]
    have h := List.getLast?_eq_getElem? (l := L)
    rw [List.getLast?_eq_some_getLast hne] at h
    exact h.symm
  have h_pre : L[pre.length]? = some u := by
    rw [hL]
    exact getElem?_consec_left _ _ _ _
  have heq : L.length - 1 = pre.length :=
    getElem?_eq_some_iff_unique_of_nodup hnd h_last h_pre
  have hlen : L.length = pre.length + 2 + suf.length := by
    rw [hL]
    simp
    ring
  omega

private lemma consec_at_pos {α : Type*} {L : List α} {a b : α} {n : ℕ}
    (hn : L[n]? = some a) (hsn : L[n + 1]? = some b) : Consec L a b := by
  rw [List.getElem?_eq_some_iff] at hn hsn
  obtain ⟨hnL, ha⟩ := hn
  obtain ⟨hsnL, hb⟩ := hsn
  refine ⟨L.take n, L.drop (n + 2), ?_⟩
  have h1 : L = L.take n ++ L.drop n := (List.take_append_drop n L).symm
  have h2 : L.drop n = a :: L.drop (n + 1) := by
    rw [← List.getElem_cons_drop hnL, ha]
  have h3 : L.drop (n + 1) = b :: L.drop (n + 2) := by
    rw [← List.getElem_cons_drop hsnL, hb]
  calc
    L = L.take n ++ L.drop n := h1
    _ = L.take n ++ a :: L.drop (n + 1) := by rw [h2]
    _ = L.take n ++ a :: b :: L.drop (n + 2) := by rw [h3]

private lemma exists_consec_pred {α : Type*} {L : List α} (hne : L ≠ [])
    {v : α} (hv : v ∈ L) (hvhead : v ≠ L.head hne) :
    ∃ u, Consec L u v := by
  obtain ⟨n, hnL, hn⟩ := List.mem_iff_getElem.mp hv
  rcases n with _ | n
  · exfalso
    apply hvhead
    rw [← hn]
    rcases L with _ | ⟨a, as⟩
    · exact absurd rfl hne
    · simp
  · have hnL' : n < L.length := Nat.lt_of_succ_lt hnL
    refine ⟨L[n], ?_⟩
    apply consec_at_pos (n := n)
    · rw [List.getElem?_eq_some_iff]
      exact ⟨hnL', rfl⟩
    · rw [List.getElem?_eq_some_iff]
      exact ⟨hnL, hn⟩

private lemma exists_consec_succ {α : Type*} {L : List α} (hne : L ≠ [])
    {v : α} (hv : v ∈ L) (hvlast : v ≠ L.getLast hne) :
    ∃ w, Consec L v w := by
  obtain ⟨n, hnL, hn⟩ := List.mem_iff_getElem.mp hv
  by_cases hnlast : n + 1 < L.length
  · refine ⟨L[n + 1], ?_⟩
    apply consec_at_pos (n := n)
    · rw [List.getElem?_eq_some_iff]
      exact ⟨hnL, hn⟩
    · rw [List.getElem?_eq_some_iff]
      exact ⟨hnlast, rfl⟩
  · push_neg at hnlast
    exfalso
    apply hvlast
    have hneq : n = L.length - 1 := by omega
    have hgl : L.getLast hne = L[L.length - 1]'(by
        have : 0 < L.length := List.length_pos_iff.mpr hne
        omega) := by
      have hL := List.getLast?_eq_some_getLast hne
      rw [List.getLast?_eq_getElem?] at hL
      rw [List.getElem?_eq_some_iff] at hL
      obtain ⟨_, hg⟩ := hL
      exact hg.symm
    rw [hgl, ← hn]
    congr

open scoped Classical in
/-- Edge indicator of the consecutive pairs in a list. -/
private noncomputable def pathIndicator {n : ℕ}
    (L : List (Fin n)) (u w : Fin n) : ℤ :=
  if Consec L u w then 1 else 0

private noncomputable def pathRank {n : ℕ}
    (L : List (Fin n)) (v : Fin n) : ℕ :=
  L.idxOf v

private lemma pathIndicator_eq_one_iff {n : ℕ}
    (L : List (Fin n)) (u w : Fin n) :
    pathIndicator L u w = 1 ↔ Consec L u w := by
  classical
  unfold pathIndicator
  by_cases h : Consec L u w <;> simp [h]

private lemma pathIndicator_eq_zero_iff {n : ℕ}
    (L : List (Fin n)) (u w : Fin n) :
    pathIndicator L u w = 0 ↔ ¬ Consec L u w := by
  classical
  unfold pathIndicator
  by_cases h : Consec L u w <;> simp [h]

private lemma pathIndicator_binary {n : ℕ}
    (L : List (Fin n)) (u w : Fin n) :
    pathIndicator L u w = 0 ∨ pathIndicator L u w = 1 := by
  classical
  unfold pathIndicator
  by_cases h : Consec L u w
  · right
    simp [h]
  · left
    simp [h]

private lemma sum_pathIndicator_in_eq {n : ℕ}
    (L : List (Fin n)) (hnd : L.Nodup) (v : Fin n) :
    ∑ i : Fin n, pathIndicator L i v =
      (@ite ℤ (∃ u, Consec L u v) (Classical.dec _) 1 0) := by
  classical
  by_cases h : ∃ u, Consec L u v
  · obtain ⟨u, hu⟩ := h
    rw [if_pos (⟨u, hu⟩ : ∃ u, Consec L u v)]
    have hfilter : (Finset.univ : Finset (Fin n)).filter
        (fun i => Consec L i v) = {u} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun hx => consec_pred_unique hnd hx hu, fun hx => hx ▸ hu⟩
    have heq : ∑ i : Fin n, pathIndicator L i v
        = ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => Consec L i v),
            (1 : ℤ) := by
      unfold pathIndicator
      rw [← Finset.sum_filter]
    rw [heq, hfilter]
    simp
  · rw [if_neg h]
    push_neg at h
    have hzero : ∀ i : Fin n, pathIndicator L i v = 0 := fun i => by
      unfold pathIndicator
      simp [h i]
    simp [hzero]

private lemma sum_pathIndicator_out_eq {n : ℕ}
    (L : List (Fin n)) (hnd : L.Nodup) (v : Fin n) :
    ∑ j : Fin n, pathIndicator L v j =
      (@ite ℤ (∃ w, Consec L v w) (Classical.dec _) 1 0) := by
  classical
  by_cases h : ∃ w, Consec L v w
  · obtain ⟨w, hw⟩ := h
    rw [if_pos (⟨w, hw⟩ : ∃ w, Consec L v w)]
    have hfilter : (Finset.univ : Finset (Fin n)).filter
        (fun j => Consec L v j) = {w} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun hx => consec_succ_unique hnd hx hw, fun hx => hx ▸ hw⟩
    have heq : ∑ j : Fin n, pathIndicator L v j
        = ∑ j ∈ (Finset.univ : Finset (Fin n)).filter (fun j => Consec L v j),
            (1 : ℤ) := by
      unfold pathIndicator
      rw [← Finset.sum_filter]
    rw [heq, hfilter]
    simp
  · rw [if_neg h]
    push_neg at h
    have hzero : ∀ j : Fin n, pathIndicator L v j = 0 := fun j => by
      unfold pathIndicator
      simp [h j]
    simp [hzero]

private lemma sum_pathIndicator_in_le_one {n : ℕ}
    (L : List (Fin n)) (hnd : L.Nodup) (v : Fin n) :
    ∑ i : Fin n, pathIndicator L i v ≤ 1 := by
  rw [sum_pathIndicator_in_eq L hnd v]
  by_cases h : ∃ u, Consec L u v <;> simp [h]

private lemma sum_pathIndicator_out_le_one {n : ℕ}
    (L : List (Fin n)) (hnd : L.Nodup) (v : Fin n) :
    ∑ j : Fin n, pathIndicator L v j ≤ 1 := by
  rw [sum_pathIndicator_out_eq L hnd v]
  by_cases h : ∃ w, Consec L v w <;> simp [h]

private lemma pathRank_consec {n : ℕ}
    (L : List (Fin n)) (hnd : L.Nodup)
    {u w : Fin n} (hc : Consec L u w) :
    pathRank L w = pathRank L u + 1 := by
  obtain ⟨pre, suf, hL⟩ := hc
  unfold pathRank
  have hu_pos : L[pre.length]? = some u := by
    rw [hL]
    exact getElem?_consec_left _ _ _ _
  have hw_pos : L[pre.length + 1]? = some w := by
    rw [hL]
    exact getElem?_consec_right _ _ _ _
  rw [List.getElem?_eq_some_iff] at hu_pos hw_pos
  obtain ⟨huL, hu⟩ := hu_pos
  obtain ⟨hwL, hw⟩ := hw_pos
  have hidx_u : L.idxOf u = pre.length := by
    rw [← hu]
    exact List.Nodup.idxOf_getElem hnd _ huL
  have hidx_w : L.idxOf w = pre.length + 1 := by
    rw [← hw]
    exact List.Nodup.idxOf_getElem hnd _ hwL
  omega

/-- A nonempty nodup graph walk from a supplier to a beneficiary induces a
valid path. -/
private lemma exists_valid_path_of_walk
    {nN nS nB : ℕ}
    (S : Fin nS → Fin nN) (B : Fin nB → Fin nN)
    (E : Fin nN → Fin nN → ℤ)
    (hE_bin : ∀ i j : Fin nN, E i j = 0 ∨ E i j = 1)
    (hSTB_disj_SB : ∀ (s : Fin nS) (b : Fin nB), S s ≠ B b)
    (L : List (Fin nN))
    (hne : L ≠ [])
    (hnd : L.Nodup)
    (hchain : L.IsChain (fun u w => E u w = 1))
    (s : Fin nS) (hs : L.head hne = S s)
    (b : Fin nB) (hb : L.getLast hne = B b) :
    P20.b.IsValidPath S B E (pathIndicator L) (pathRank L) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pathIndicator_binary L
  · intro i j
    by_cases hc : Consec L i j
    · have h1 : pathIndicator L i j = 1 :=
        (pathIndicator_eq_one_iff L i j).mpr hc
      have hE1 : E i j = 1 :=
        consec_chain (R := fun u w => E u w = 1) hchain hc
      rw [h1, hE1]
    · have h0 : pathIndicator L i j = 0 :=
        (pathIndicator_eq_zero_iff L i j).mpr hc
      rw [h0]
      rcases hE_bin i j with hE0 | hE1
      · rw [hE0]
      · rw [hE1]
        norm_num
  · exact sum_pathIndicator_in_le_one L hnd
  · exact sum_pathIndicator_out_le_one L hnd
  · refine ⟨s, ?_, ?_, ?_⟩
    · rw [sum_pathIndicator_out_eq L hnd]
      have hsucc : ∃ w, Consec L (S s) w := by
        apply exists_consec_succ hne
        · rw [← hs]
          exact List.head_mem hne
        · rw [hb]
          exact hSTB_disj_SB s b
      rw [if_pos hsucc]
    · rw [sum_pathIndicator_in_eq L hnd]
      have hno : ¬∃ u, Consec L u (S s) := by
        rintro ⟨u, hu⟩
        rcases L with _ | ⟨a, as⟩
        · exact hne rfl
        · have ha : a = S s := by simpa using hs
          subst a
          exact consec_no_pred_head hnd u hu
      rw [if_neg hno]
    · intro v hv
      have hsucc : ∃ w, Consec L v w := by
        rw [sum_pathIndicator_out_eq L hnd] at hv
        by_cases he : ∃ w, Consec L v w
        · exact he
        · rw [if_neg he] at hv
          norm_num at hv
      have hnopred : ¬∃ u, Consec L u v := by
        intro he
        have hin := hv.2
        rw [sum_pathIndicator_in_eq L hnd, if_pos he] at hin
        norm_num at hin
      have hvmem : v ∈ L := by
        obtain ⟨w, hw⟩ := hsucc
        exact consec_left_mem hw
      by_contra hvs
      have hvhead : v ≠ L.head hne := by
        rw [hs]
        exact hvs
      exact hnopred (exists_consec_pred hne hvmem hvhead)
  · refine ⟨b, ?_, ?_, ?_⟩
    · rw [sum_pathIndicator_in_eq L hnd]
      have hpred : ∃ u, Consec L u (B b) := by
        apply exists_consec_pred hne
        · rw [← hb]
          exact List.getLast_mem hne
        · rw [hs]
          exact (hSTB_disj_SB s b).symm
      rw [if_pos hpred]
    · rw [sum_pathIndicator_out_eq L hnd]
      have hno : ¬∃ w, Consec L (B b) w := by
        rintro ⟨w, hw⟩
        rw [← hb] at hw
        exact consec_no_succ_last hne hnd w hw
      rw [if_neg hno]
    · intro v hv
      have hpred : ∃ u, Consec L u v := by
        rw [sum_pathIndicator_in_eq L hnd] at hv
        by_cases he : ∃ u, Consec L u v
        · exact he
        · rw [if_neg he] at hv
          norm_num at hv
      have hnosucc : ¬∃ w, Consec L v w := by
        intro he
        have hout := hv.2
        rw [sum_pathIndicator_out_eq L hnd, if_pos he] at hout
        norm_num at hout
      have hvmem : v ∈ L := by
        obtain ⟨u, hu⟩ := hpred
        exact consec_right_mem hu
      by_contra hvb
      have hvlast : v ≠ L.getLast hne := by
        rw [hb]
        exact hvb
      exact hnosucc (exists_consec_succ hne hvmem hvlast)
  · intro i j hij
    exact pathRank_consec L hnd ((pathIndicator_eq_one_iff L i j).mp hij)

open scoped Classical in
private noncomputable def cycleIndicator {n m : ℕ}
    (verts : Fin m → Fin n) (u w : Fin n) : ℤ :=
  if ∃ i : Fin m, verts i = u ∧ verts (finRotate m i) = w then 1 else 0

private lemma cycleIndicator_eq_one_iff {n m : ℕ}
    (verts : Fin m → Fin n) (u w : Fin n) :
    cycleIndicator verts u w = 1 ↔
      ∃ i : Fin m, verts i = u ∧ verts (finRotate m i) = w := by
  classical
  unfold cycleIndicator
  by_cases h : ∃ i : Fin m, verts i = u ∧ verts (finRotate m i) = w <;> simp [h]

private lemma cycleIndicator_binary {n m : ℕ}
    (verts : Fin m → Fin n) (u w : Fin n) :
    cycleIndicator verts u w = 0 ∨ cycleIndicator verts u w = 1 := by
  classical
  unfold cycleIndicator
  by_cases h : ∃ i : Fin m, verts i = u ∧ verts (finRotate m i) = w <;> simp [h]

private lemma sum_cycleIndicator_out_eq {n m : ℕ}
    (verts : Fin m → Fin n) (hinj : Function.Injective verts) (v : Fin n) :
    ∑ w : Fin n, cycleIndicator verts v w =
      if ∃ i : Fin m, verts i = v then 1 else 0 := by
  classical
  by_cases h : ∃ i : Fin m, verts i = v
  · obtain ⟨i, hi⟩ := h
    rw [if_pos ⟨i, hi⟩]
    have hfilter : (Finset.univ : Finset (Fin n)).filter
        (fun w => ∃ j : Fin m, verts j = v ∧ verts (finRotate m j) = w) =
        {verts (finRotate m i)} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨j, hjv, rfl⟩
        have hji : j = i := hinj (hjv.trans hi.symm)
        subst j
        rfl
      · intro hw
        exact ⟨i, hi, hw.symm⟩
    have heq :
        ∑ w : Fin n, cycleIndicator verts v w =
          ∑ w ∈ (Finset.univ : Finset (Fin n)).filter
              (fun w => ∃ j : Fin m, verts j = v ∧ verts (finRotate m j) = w),
            (1 : ℤ) := by
      unfold cycleIndicator
      rw [← Finset.sum_filter]
    rw [heq, hfilter]
    simp
  · rw [if_neg h]
    push_neg at h
    have hz : ∀ w : Fin n, cycleIndicator verts v w = 0 := by
      intro w
      unfold cycleIndicator
      simp [h]
    simp [hz]

private lemma sum_cycleIndicator_in_eq {n m : ℕ}
    (verts : Fin m → Fin n) (hinj : Function.Injective verts) (v : Fin n) :
    ∑ u : Fin n, cycleIndicator verts u v =
      if ∃ i : Fin m, verts i = v then 1 else 0 := by
  classical
  by_cases h : ∃ i : Fin m, verts i = v
  · obtain ⟨i, hi⟩ := h
    let j : Fin m := (finRotate m).symm i
    have hj : finRotate m j = i := (finRotate m).apply_symm_apply i
    rw [if_pos ⟨i, hi⟩]
    have hfilter : (Finset.univ : Finset (Fin n)).filter
        (fun u => ∃ k : Fin m, verts k = u ∧ verts (finRotate m k) = v) =
        {verts j} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨k, rfl, hkv⟩
        have hrot : finRotate m k = i := hinj (hkv.trans hi.symm)
        have hkj : k = j := (finRotate m).injective (hrot.trans hj.symm)
        subst k
        rfl
      · intro hu
        refine ⟨j, hu.symm, ?_⟩
        rw [hj, hi]
    have heq :
        ∑ u : Fin n, cycleIndicator verts u v =
          ∑ u ∈ (Finset.univ : Finset (Fin n)).filter
              (fun u => ∃ k : Fin m, verts k = u ∧ verts (finRotate m k) = v),
            (1 : ℤ) := by
      unfold cycleIndicator
      rw [← Finset.sum_filter]
    rw [heq, hfilter]
    simp
  · rw [if_neg h]
    push_neg at h
    have hz : ∀ u : Fin n, cycleIndicator verts u v = 0 := by
      intro u
      unfold cycleIndicator
      apply if_neg
      rintro ⟨k, -, hkv⟩
      exact h (finRotate m k) hkv
    simp [hz]

private lemma snoc_succ_eq_rotate {n m : ℕ} (hm : 0 < m)
    (verts : Fin m → Fin n) (i : Fin m) :
    @Fin.snoc m (fun _ => Fin n) verts (verts ⟨0, hm⟩) i.succ =
      verts (finRotate m i) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  by_cases hi : i = Fin.last q
  · subst i
    simp
  · have hlt : (i : ℕ) < q := Fin.val_lt_last hi
    have heq : i.succ = (finRotate (q + 1) i).castSucc := by
      ext
      rw [Fin.val_succ, Fin.val_castSucc, coe_finRotate_of_ne_last hi]
    rw [heq, Fin.snoc_castSucc]

private lemma valid_cycle_of_rotate
    {n m : ℕ}
    (E : Fin n → Fin n → ℤ)
    (hEbin : ∀ u w, E u w = 0 ∨ E u w = 1)
    (hm : 0 < m)
    (verts : Fin m → Fin n)
    (hinj : Function.Injective verts)
    (hedge : ∀ i, E (verts i) (verts (finRotate m i)) = 1) :
    P20.b.IsValidCycle E (cycleIndicator verts) := by
  classical
  refine ⟨cycleIndicator_binary verts, ?_, ?_, ?_, ?_, ?_⟩
  · intro u w
    by_cases hc : ∃ i, verts i = u ∧ verts (finRotate m i) = w
    · obtain ⟨i, rfl, rfl⟩ := hc
      rw [(cycleIndicator_eq_one_iff verts _ _).mpr ⟨i, rfl, rfl⟩, hedge]
    · have hzero : cycleIndicator verts u w = 0 := by
        unfold cycleIndicator
        simp [hc]
      rw [hzero]
      rcases hEbin u w with h | h <;> omega
  · intro v
    rw [sum_cycleIndicator_in_eq verts hinj v]
    split <;> omega
  · intro v
    rw [sum_cycleIndicator_out_eq verts hinj v]
    split <;> omega
  · intro v
    rw [sum_cycleIndicator_in_eq verts hinj v,
      sum_cycleIndicator_out_eq verts hinj v]
  · let z : Fin m := ⟨0, hm⟩
    let closed : Fin (m + 1) → Fin n := Fin.snoc verts (verts z)
    refine ⟨m, closed, hm, ?_, ?_, ?_⟩
    · have hzero : closed 0 = verts z := by
        change @Fin.snoc m (fun _ => Fin n) verts (verts z) 0 = verts z
        have hz : (0 : Fin (m + 1)) = z.castSucc := Fin.ext rfl
        rw [hz, Fin.snoc_castSucc]
      have hlast : closed (Fin.last m) = verts z := by
        change @Fin.snoc m (fun _ => Fin n) verts (verts z) (Fin.last m) = verts z
        rw [Fin.snoc_last]
      exact hzero.trans hlast.symm
    · intro i j hi hj hij
      have hilast : i ≠ Fin.last m := ne_of_lt hi
      have hjlast : j ≠ Fin.last m := ne_of_lt hj
      obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hilast
      obtain ⟨j', rfl⟩ := Fin.eq_castSucc_of_ne_last hjlast
      simp only [closed, Fin.snoc_castSucc] at hij
      exact congrArg Fin.castSucc (hinj hij)
    · intro u w
      rw [cycleIndicator_eq_one_iff]
      constructor
      · rintro ⟨i, rfl, rfl⟩
        refine ⟨i, ?_, ?_⟩
        · simp [closed]
        · simp only [closed]
          exact snoc_succ_eq_rotate hm verts i
      · rintro ⟨i, hi, hw⟩
        refine ⟨i, ?_, ?_⟩
        · simpa [closed] using hi
        · rw [← snoc_succ_eq_rotate hm verts i]
          exact hw

private lemma valid_cycle_of_list
    {n : ℕ}
    (E : Fin n → Fin n → ℤ)
    (hEbin : ∀ u w, E u w = 0 ∨ E u w = 1)
    (L : List (Fin n)) (hne : L ≠ []) (hnd : L.Nodup)
    (hchain : L.IsChain (fun u w => E u w = 1))
    (hclose : E (L.getLast hne) (L.head hne) = 1) :
    P20.b.IsValidCycle E (cycleIndicator L.get) := by
  classical
  rcases L with _ | ⟨a, as⟩
  · exact absurd rfl hne
  · apply valid_cycle_of_rotate E hEbin (by simp) (a :: as).get hnd.injective_get
    · intro i
      by_cases hi : i = Fin.last as.length
      · subst i
        simpa [List.getLast_eq_getElem, finRotate_last] using hclose
      · have hlt : (i : ℕ) < as.length := Fin.val_lt_last hi
        have hedge := hchain.getElem i (by simp only [List.length_cons]; omega)
        have hrot : (finRotate (as.length + 1) i : ℕ) = i + 1 :=
          coe_finRotate_of_ne_last hi
        change E ((a :: as).get i) ((a :: as).get (finRotate (as.length + 1) i)) = 1
        have hrotfin :
            finRotate (as.length + 1) i =
              ⟨i + 1, by simp only [List.length_cons] at hedge; omega⟩ :=
          Fin.ext hrot
        rw [hrotfin]
        exact hedge

-- ============================================================================
-- § Per-commodity structural flows
-- ============================================================================

/-- The homogeneous network constraints used by the decomposition induction.
Demand and nutrition are deliberately absent: subtracting a path need not
preserve them. -/
private structure StructuralFlow (f : Fin pa.nN → Fin pa.nN → ℝ) : Prop where
  supplier_in : ∀ s : Fin pa.nS, ∑ i, f i (pa.S s) = 0
  transshipment : ∀ t : Fin pa.nT,
    ∑ i, f i (pa.T t) = ∑ j, f (pa.T t) j
  beneficiary_out : ∀ b : Fin pa.nB, ∑ j, f (pa.B b) j = 0
  offedge : ∀ i j, pa.E i j = 0 → f i j = 0

private lemma edge_mul_flow_eq (v : P20.a.Vars pa) (h : P20.a.Feasible pa v)
    (i j : Fin pa.nN) (k : Fin pa.nK) :
    (pa.E i j : ℝ) * v.F i j k = v.F i j k := by
  rcases pa.hE_bin i j with hE | hE
  · rw [hE, Int.cast_zero, zero_mul, h.hF_offedge i j k hE]
  · simp [hE]

private lemma feasible_structural (v : P20.a.Vars pa) (h : P20.a.Feasible pa v)
    (k : Fin pa.nK) :
    StructuralFlow pa (fun i j => v.F i j k) := by
  refine ⟨?_, ?_, ?_, h.hF_offedge (k := k)⟩
  · intro s
    apply Finset.sum_eq_zero
    intro i _
    exact h.hF_offedge i (pa.S s) k (pa.hE_noinflow_S i s)
  · intro t
    simpa only [edge_mul_flow_eq pa v h] using h.hflow t k
  · intro b
    apply Finset.sum_eq_zero
    intro j _
    exact h.hF_offedge (pa.B b) j k (pa.hE_nooutflow_B b j)

private lemma sum_eq_zero_term_eq_zero {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (hnn : ∀ i, 0 ≤ g i) (hsum : ∑ i, g i = 0) (i : ι) :
    g i = 0 := by
  have hle : g i ≤ ∑ j, g j := Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
  rw [hsum] at hle
  exact le_antisymm hle (hnn i)

private lemma structural_no_supplier_in
    (f : Fin pa.nN → Fin pa.nN → ℝ) (hf : StructuralFlow pa f)
    (hnn : ∀ i j, 0 ≤ f i j) (s : Fin pa.nS) (i : Fin pa.nN) :
    f i (pa.S s) = 0 :=
  sum_eq_zero_term_eq_zero _ (fun j => hnn j (pa.S s)) (hf.supplier_in s) i

private lemma structural_no_beneficiary_out
    (f : Fin pa.nN → Fin pa.nN → ℝ) (hf : StructuralFlow pa f)
    (hnn : ∀ i j, 0 ≤ f i j) (b : Fin pa.nB) (j : Fin pa.nN) :
    f (pa.B b) j = 0 :=
  sum_eq_zero_term_eq_zero _ (hnn (pa.B b)) (hf.beneficiary_out b) j

private lemma exists_pos_of_sum_pos {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (hnn : ∀ i, 0 ≤ g i) (hpos : 0 < ∑ i, g i) :
    ∃ i, 0 < g i := by
  by_contra h
  push_neg at h
  have hz : ∀ i, g i = 0 := fun i => le_antisymm (h i) (hnn i)
  simp [hz] at hpos

private lemma structural_pos_out_of_pos_in
    (f : Fin pa.nN → Fin pa.nN → ℝ) (hf : StructuralFlow pa f)
    (hnn : ∀ i j, 0 ≤ f i j) (t : Fin pa.nT) {i : Fin pa.nN}
    (hi : 0 < f i (pa.T t)) :
    ∃ j, 0 < f (pa.T t) j := by
  have hin : 0 < ∑ q, f q (pa.T t) := by
    have hle : f i (pa.T t) ≤ ∑ q, f q (pa.T t) :=
      Finset.single_le_sum (fun q _ => hnn q (pa.T t)) (Finset.mem_univ i)
    linarith
  rw [hf.transshipment t] at hin
  exact exists_pos_of_sum_pos _ (hnn (pa.T t)) hin

private lemma structural_pos_in_of_pos_out
    (f : Fin pa.nN → Fin pa.nN → ℝ) (hf : StructuralFlow pa f)
    (hnn : ∀ i j, 0 ≤ f i j) (t : Fin pa.nT) {j : Fin pa.nN}
    (hj : 0 < f (pa.T t) j) :
    ∃ i, 0 < f i (pa.T t) := by
  have hout : 0 < ∑ q, f (pa.T t) q := by
    have hle : f (pa.T t) j ≤ ∑ q, f (pa.T t) q :=
      Finset.single_le_sum (fun q _ => hnn (pa.T t) q) (Finset.mem_univ j)
    linarith
  rw [← hf.transshipment t] at hout
  exact exists_pos_of_sum_pos _ (fun i => hnn i (pa.T t)) hout

private lemma structural_positive_edge_is_edge
    (f : Fin pa.nN → Fin pa.nN → ℝ) (hf : StructuralFlow pa f)
    {i j : Fin pa.nN} (hpos : 0 < f i j) :
    pa.E i j = 1 := by
  rcases pa.hE_bin i j with hE | hE
  · exact absurd (hf.offedge i j hE) (ne_of_gt hpos)
  · exact hE

private lemma structural_node_is_transshipment
    (f : Fin pa.nN → Fin pa.nN → ℝ) (hf : StructuralFlow pa f)
    (hnn : ∀ i j, 0 ≤ f i j) (v : Fin pa.nN)
    (hin : ∃ i, 0 < f i v) (hout : ∃ j, 0 < f v j) :
    ∃ t : Fin pa.nT, pa.T t = v := by
  rcases pa.hSTB_partition v with ⟨s, hs⟩ | ⟨t, ht⟩ | ⟨b, hb⟩
  · obtain ⟨i, hi⟩ := hin
    rw [← hs, structural_no_supplier_in pa f hf hnn s i] at hi
    norm_num at hi
  · exact ⟨t, ht⟩
  · obtain ⟨j, hj⟩ := hout
    rw [← hb, structural_no_beneficiary_out pa f hf hnn b j] at hj
    norm_num at hj

private def PosWalk
    (f : Fin pa.nN → Fin pa.nN → ℝ) (L : List (Fin pa.nN)) : Prop :=
  L.Nodup ∧ 2 ≤ L.length ∧ L.IsChain (fun u w => 0 < f u w)

private lemma exists_maximal_pos_walk
    (f : Fin pa.nN → Fin pa.nN → ℝ)
    {i j : Fin pa.nN} (hij : i ≠ j) (hpos : 0 < f i j) :
    ∃ L : List (Fin pa.nN),
      PosWalk pa f L ∧
      ∀ L' : List (Fin pa.nN), PosWalk pa f L' → L'.length ≤ L.length := by
  classical
  let W : ℕ → Prop := fun r =>
    ∃ L : List (Fin pa.nN), PosWalk pa f L ∧ L.length = r
  have hbase : W 2 := by
    refine ⟨[i, j], ?_, rfl⟩
    refine ⟨by simp [hij], by simp, ?_⟩
    simpa using hpos
  have htwo_le : 2 ≤ pa.nN := by
    have hnd : ([i, j] : List (Fin pa.nN)).Nodup := by simp [hij]
    simpa using hnd.length_le_card
  let r := Nat.findGreatest W pa.nN
  have hr : W r := Nat.findGreatest_spec htwo_le hbase
  obtain ⟨L, hL, hlen⟩ := hr
  refine ⟨L, hL, ?_⟩
  intro L' hL'
  have hbound : L'.length ≤ pa.nN := by
    simpa using hL'.1.length_le_card
  have hle : L'.length ≤ r :=
    Nat.le_findGreatest hbound ⟨L', hL', rfl⟩
  rwa [← hlen] at hle

private lemma pred_mem_of_maximal_pos_walk
    (f : Fin pa.nN → Fin pa.nN → ℝ)
    (L : List (Fin pa.nN)) (hL : PosWalk pa f L)
    (hmax : ∀ L', PosWalk pa f L' → L'.length ≤ L.length)
    (hne : L ≠ []) (u : Fin pa.nN) (hu : 0 < f u (L.head hne)) :
    u ∈ L := by
  classical
  change L.Nodup ∧ 2 ≤ L.length ∧ L.IsChain (fun u w => 0 < f u w) at hL
  obtain ⟨hnd, hlen, hchain⟩ := hL
  by_contra humem
  have hnew : PosWalk pa f (u :: L) := by
    refine ⟨by simpa using ⟨humem, hnd⟩, by simp; omega, ?_⟩
    exact hchain.cons_of_ne_nil hne hu
  have := hmax (u :: L) hnew
  simp at this

private lemma succ_mem_of_maximal_pos_walk
    (f : Fin pa.nN → Fin pa.nN → ℝ)
    (L : List (Fin pa.nN)) (hL : PosWalk pa f L)
    (hmax : ∀ L', PosWalk pa f L' → L'.length ≤ L.length)
    (hne : L ≠ []) (w : Fin pa.nN) (hw : 0 < f (L.getLast hne) w) :
    w ∈ L := by
  classical
  change L.Nodup ∧ 2 ≤ L.length ∧ L.IsChain (fun u w => 0 < f u w) at hL
  obtain ⟨hnd, hlen, hchain⟩ := hL
  by_contra hwmem
  have hnew : PosWalk pa f (L ++ [w]) := by
    refine ⟨?_, by simp; omega, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hnd, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      intro hab
      apply hwmem
      rw [← hab]
      exact ha
    · apply hchain.append (List.isChain_singleton w)
      intro x hx y hy
      have hx' : x = L.getLast hne := by
        rw [List.getLast?_eq_some_getLast hne] at hx
        exact (Option.some.inj hx).symm
      have hy' : y = w := by simpa using hy.symm
      simpa [hx', hy'] using hw
  have := hmax (L ++ [w]) hnew
  simp at this

private lemma cycle_list_nodes_transshipment
    (f : Fin pa.nN → Fin pa.nN → ℝ) (hf : StructuralFlow pa f)
    (hnn : ∀ i j, 0 ≤ f i j)
    (C : List (Fin pa.nN)) (hne : C ≠ [])
    (hchain : C.IsChain (fun u w => 0 < f u w))
    (hclose : 0 < f (C.getLast hne) (C.head hne)) :
    ∀ v ∈ C, ∃ t : Fin pa.nT, pa.T t = v := by
  intro v hv
  apply structural_node_is_transshipment pa f hf hnn v
  · by_cases hvh : v = C.head hne
    · exact ⟨C.getLast hne, by simpa [hvh] using hclose⟩
    · obtain ⟨u, hu⟩ := exists_consec_pred hne hv hvh
      exact ⟨u, consec_chain (R := fun u w => 0 < f u w) hchain hu⟩
  · by_cases hvl : v = C.getLast hne
    · exact ⟨C.head hne, by simpa [hvl] using hclose⟩
    · obtain ⟨w, hw⟩ := exists_consec_succ hne hv hvl
      exact ⟨w, consec_chain (R := fun u w => 0 < f u w) hchain hw⟩

private lemma head_ne_getLast_of_nodup_two
    {α : Type*} {L : List α} (hne : L ≠ []) (hnd : L.Nodup)
    (hlen : 2 ≤ L.length) :
    L.head hne ≠ L.getLast hne := by
  rcases L with _ | ⟨a, as⟩
  · exact absurd rfl hne
  · rcases as with _ | ⟨b, bs⟩
    · simp at hlen
    · intro heq
      rw [List.nodup_cons] at hnd
      apply hnd.1
      have halast : a = (a :: b :: bs).getLast hne := by simpa using heq
      rw [halast]
      exact List.getLast_mem (by simp)

private lemma closed_prefix_of_mem
    {α : Type*} {R : α → α → Prop} {L : List α}
    (hne : L ≠ []) (hnd : L.Nodup) (hchain : L.IsChain R)
    {u : α} (hu : u ∈ L) (hclose : R u (L.head hne)) :
    ∃ C : List α, ∃ hCne : C ≠ [], C.Nodup ∧ C.IsChain R ∧
      R (C.getLast hCne) (C.head hCne) := by
  obtain ⟨pre, suf, hEq⟩ := List.mem_iff_append.mp hu
  subst L
  let C := pre ++ [u]
  have hCne : C ≠ [] := by simp [C]
  have hCnd : C.Nodup := by
    have ht := hnd.take (i := pre.length + 1)
    have heq : (pre ++ u :: suf).take (pre.length + 1) = C := by
      simp [C, List.take_append]
    rwa [heq] at ht
  have hCchain : C.IsChain R := by
    have ht := hchain.take (pre.length + 1)
    have heq : (pre ++ u :: suf).take (pre.length + 1) = C := by
      simp [C, List.take_append]
    rwa [heq] at ht
  have hheadL : (pre ++ u :: suf).head hne = C.head hCne := by
    rcases pre with _ | ⟨a, as⟩ <;> simp [C]
  have hlastC : C.getLast hCne = u := by simp [C]
  refine ⟨C, hCne, hCnd, hCchain, ?_⟩
  rwa [hlastC, ← hheadL]

private lemma closed_suffix_of_mem
    {α : Type*} {R : α → α → Prop} {L : List α}
    (hne : L ≠ []) (hnd : L.Nodup) (hchain : L.IsChain R)
    {u : α} (hu : u ∈ L) (hclose : R (L.getLast hne) u) :
    ∃ C : List α, ∃ hCne : C ≠ [], C.Nodup ∧ C.IsChain R ∧
      R (C.getLast hCne) (C.head hCne) := by
  obtain ⟨pre, suf, hEq⟩ := List.mem_iff_append.mp hu
  subst L
  let C := u :: suf
  have hCne : C ≠ [] := by simp [C]
  have hCnd : C.Nodup := by
    have hd := hnd.drop (i := pre.length)
    have heq : (pre ++ u :: suf).drop pre.length = C := by simp [C]
    rwa [heq] at hd
  have hCchain : C.IsChain R := by
    have := hchain.drop pre.length
    have heq : (pre ++ u :: suf).drop pre.length = C := by simp [C]
    rwa [heq] at this
  have hlastL : (pre ++ u :: suf).getLast hne = C.getLast hCne := by
    change (pre ++ C).getLast hne = C.getLast hCne
    exact List.getLast_append_of_right_ne_nil pre C hCne
  have hheadC : C.head hCne = u := by simp [C]
  refine ⟨C, hCne, hCnd, hCchain, ?_⟩
  rwa [← hlastL, hheadC]

private lemma exists_positive_path_or_cycle_list
    (f : Fin pa.nN → Fin pa.nN → ℝ) (hf : StructuralFlow pa f)
    (hnn : ∀ i j, 0 ≤ f i j) (i j : Fin pa.nN) (hpos : 0 < f i j) :
    (∃ L : List (Fin pa.nN), ∃ hne : L ≠ [],
      L.Nodup ∧ L.IsChain (fun u w => 0 < f u w) ∧
      (∃ s, L.head hne = pa.S s) ∧ (∃ b, L.getLast hne = pa.B b)) ∨
    (∃ C : List (Fin pa.nN), ∃ hne : C ≠ [],
      C.Nodup ∧ C.IsChain (fun u w => 0 < f u w) ∧
      0 < f (C.getLast hne) (C.head hne)) := by
  classical
  by_cases hij : i = j
  · subst j
    right
    refine ⟨[i], by simp, by simp, by simp, ?_⟩
    simpa using hpos
  · obtain ⟨L, hL, hmax⟩ := exists_maximal_pos_walk pa f hij hpos
    change L.Nodup ∧ 2 ≤ L.length ∧ L.IsChain (fun u w => 0 < f u w) at hL
    obtain ⟨hnd, hlen, hchain⟩ := hL
    have hne : L ≠ [] := by
      apply List.ne_nil_of_length_pos
      omega
    have hhl : L.head hne ≠ L.getLast hne :=
      head_ne_getLast_of_nodup_two hne hnd hlen
    obtain ⟨w₀, hw₀⟩ := exists_consec_succ hne (List.head_mem hne) hhl
    have hout_head : 0 < f (L.head hne) w₀ :=
      consec_chain (R := fun u w => 0 < f u w) hchain hw₀
    obtain ⟨u₀, hu₀⟩ :=
      exists_consec_pred hne (List.getLast_mem hne) hhl.symm
    have hin_last : 0 < f u₀ (L.getLast hne) :=
      consec_chain (R := fun u w => 0 < f u w) hchain hu₀
    rcases pa.hSTB_partition (L.head hne) with
      ⟨s, hs⟩ | ⟨t, ht⟩ | ⟨b, hb⟩
    · rcases pa.hSTB_partition (L.getLast hne) with
        ⟨s', hs'⟩ | ⟨t', ht'⟩ | ⟨b, hb'⟩
      · rw [← hs', structural_no_supplier_in pa f hf hnn s' u₀] at hin_last
        norm_num at hin_last
      · have hinT : 0 < f u₀ (pa.T t') := by simpa [ht'] using hin_last
        obtain ⟨w, hw⟩ := structural_pos_out_of_pos_in pa f hf hnn t' hinT
        have hw' : 0 < f (L.getLast hne) w := by simpa [ht'] using hw
        have hwmem := succ_mem_of_maximal_pos_walk pa f L
          ⟨hnd, hlen, hchain⟩ hmax hne w hw'
        obtain ⟨C, hCne, hCnd, hCchain, hCclose⟩ :=
          closed_suffix_of_mem hne hnd hchain hwmem hw'
        exact Or.inr ⟨C, hCne, hCnd, hCchain, hCclose⟩
      · exact Or.inl ⟨L, hne, hnd, hchain, ⟨s, hs.symm⟩, ⟨b, hb'.symm⟩⟩
    · have houtT : 0 < f (pa.T t) w₀ := by simpa [ht] using hout_head
      obtain ⟨u, hu⟩ := structural_pos_in_of_pos_out pa f hf hnn t houtT
      have hu' : 0 < f u (L.head hne) := by simpa [ht] using hu
      have humem := pred_mem_of_maximal_pos_walk pa f L
        ⟨hnd, hlen, hchain⟩ hmax hne u hu'
      obtain ⟨C, hCne, hCnd, hCchain, hCclose⟩ :=
        closed_prefix_of_mem hne hnd hchain humem hu'
      exact Or.inr ⟨C, hCne, hCnd, hCchain, hCclose⟩
    · rw [← hb, structural_no_beneficiary_out pa f hf hnn b w₀] at hout_head
      norm_num at hout_head

private lemma cycleIndicator_list_positive
    {n : ℕ} (f : Fin n → Fin n → ℝ)
    (C : List (Fin n)) (hne : C ≠ [])
    (hchain : C.IsChain (fun u w => 0 < f u w))
    (hclose : 0 < f (C.getLast hne) (C.head hne))
    {u w : Fin n} (hc : cycleIndicator C.get u w = 1) :
    0 < f u w := by
  classical
  obtain ⟨i, hiu, hiw⟩ := (cycleIndicator_eq_one_iff C.get u w).mp hc
  rcases C with _ | ⟨a, as⟩
  · exact absurd rfl hne
  · by_cases hi : i = Fin.last as.length
    · subst i
      have hu : u = (a :: as).getLast hne := by
        rw [← hiu, List.getLast_eq_getElem]
        rfl
      have hw : w = (a :: as).head hne := by
        rw [← hiw]
        simp
      simpa [hu, hw] using hclose
    · have hlt : (i : ℕ) < as.length := Fin.val_lt_last hi
      have hedge := hchain.getElem i (by simp only [List.length_cons]; omega)
      have hrot : (finRotate (as.length + 1) i : ℕ) = i + 1 :=
        coe_finRotate_of_ne_last hi
      have hrotfin :
          finRotate (as.length + 1) i =
            ⟨i + 1, by simp only [List.length_cons] at hedge; omega⟩ :=
        Fin.ext hrot
      change (a :: as).get (finRotate (as.length + 1) i) = w at hiw
      rw [hrotfin] at hiw
      simpa [← hiu, ← hiw] using hedge

private lemma exists_positive_enumerated_atom
    (f : Fin pa.nN → Fin pa.nN → ℝ) (hf : StructuralFlow pa f)
    (hnn : ∀ i j, 0 ≤ f i j) (i j : Fin pa.nN) (hpos : 0 < f i j) :
    (∃ p : Fin (numPaths pa),
      ∀ u w, pathEnum pa p u w = 1 → 0 < f u w) ∨
    (∃ c : Fin (numCycles pa),
      ∀ u w, cycleEnum pa c u w = 1 → 0 < f u w) := by
  classical
  rcases exists_positive_path_or_cycle_list pa f hf hnn i j hpos with hpath | hcycle
  · obtain ⟨L, hne, hnd, hchain, ⟨s, hs⟩, ⟨b, hb⟩⟩ := hpath
    have hEchain : L.IsChain (fun u w => pa.E u w = 1) := by
      exact hchain.imp fun _ _ h => structural_positive_edge_is_edge pa f hf h
    have hvp := exists_valid_path_of_walk pa.S pa.B pa.E pa.hE_bin
      pa.hSTB_disj_SB L hne hnd hEchain s hs b hb
    obtain ⟨p, hp⟩ := pathEnum_complete pa (pathIndicator L) (pathRank L) hvp
    left
    refine ⟨p, ?_⟩
    intro u w huw
    have hi : pathIndicator L u w = 1 := by rw [← hp u w]; exact huw
    exact consec_chain (R := fun u w => 0 < f u w) hchain
      ((pathIndicator_eq_one_iff L u w).mp hi)
  · obtain ⟨C, hne, hnd, hchain, hclose⟩ := hcycle
    have hEchain : C.IsChain (fun u w => pa.E u w = 1) :=
      hchain.imp fun _ _ h => structural_positive_edge_is_edge pa f hf h
    have hEclose : pa.E (C.getLast hne) (C.head hne) = 1 :=
      structural_positive_edge_is_edge pa f hf hclose
    have hvc := valid_cycle_of_list pa.E pa.hE_bin C hne hnd hEchain hEclose
    obtain ⟨c, hc⟩ := cycleEnum_complete pa (cycleIndicator C.get) hvc
    right
    refine ⟨c, ?_⟩
    intro u w huw
    have hi : cycleIndicator C.get u w = 1 := by rw [← hc u w]; exact huw
    exact cycleIndicator_list_positive f C hne hchain hclose hi

private lemma path_supplier_deg_zero_aux
    (p : Fin (numPaths pa)) (s : Fin pa.nS) :
    ∑ i, pathEnum pa p i (pa.S s) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact pathEnum_zero_of_E_zero pa p i (pa.S s) (pa.hE_noinflow_S i s)

private lemma path_beneficiary_deg_zero_aux
    (p : Fin (numPaths pa)) (b : Fin pa.nB) :
    ∑ j, pathEnum pa p (pa.B b) j = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  exact pathEnum_zero_of_E_zero pa p (pa.B b) j (pa.hE_nooutflow_B b j)

private lemma path_transshipment_deg_aux
    (p : Fin (numPaths pa)) (t : Fin pa.nT) :
    ∑ i, pathEnum pa p i (pa.T t) = ∑ j, pathEnum pa p (pa.T t) j := by
  obtain ⟨hbin, -, hin1, hout1, hsrc, hsink, -⟩ := pathEnum_isValidPath pa p
  set IN := ∑ i, pathEnum pa p i (pa.T t)
  set OUT := ∑ j, pathEnum pa p (pa.T t) j
  have hIN_nn : 0 ≤ IN := Finset.sum_nonneg fun i _ => by
    rcases hbin i (pa.T t) with h | h <;> omega
  have hIN_le := hin1 (pa.T t)
  have hOUT_nn : 0 ≤ OUT := Finset.sum_nonneg fun j _ => by
    rcases hbin (pa.T t) j with h | h <;> omega
  have hOUT_le := hout1 (pa.T t)
  by_contra hne
  rcases (show (IN = 0 ∧ OUT = 1) ∨ (IN = 1 ∧ OUT = 0) by omega) with
    ⟨hI, hO⟩ | ⟨hI, hO⟩
  · obtain ⟨s, -, -, hsuniq⟩ := hsrc
    exact pa.hSTB_disj_ST s t (hsuniq (pa.T t) ⟨hO, hI⟩).symm
  · obtain ⟨b, -, -, hbuniq⟩ := hsink
    exact pa.hSTB_disj_TB t b (hbuniq (pa.T t) ⟨hI, hO⟩)

private lemma cycle_supplier_deg_zero_aux
    (c : Fin (numCycles pa)) (s : Fin pa.nS) :
    ∑ i, cycleEnum pa c i (pa.S s) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact cycleEnum_zero_of_E_zero pa c i (pa.S s) (pa.hE_noinflow_S i s)

private lemma cycle_beneficiary_deg_zero_aux
    (c : Fin (numCycles pa)) (b : Fin pa.nB) :
    ∑ j, cycleEnum pa c (pa.B b) j = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  exact cycleEnum_zero_of_E_zero pa c (pa.B b) j (pa.hE_nooutflow_B b j)

private noncomputable def decompAtom
    (a : Sum (Fin (numPaths pa)) (Fin (numCycles pa)))
    (e : Fin pa.nN × Fin pa.nN) : ℝ :=
  match a with
  | .inl p => pathEnum pa p e.1 e.2
  | .inr c => cycleEnum pa c e.1 e.2

private lemma decompAtom_binary
    (a : Sum (Fin (numPaths pa)) (Fin (numCycles pa))) (e : Fin pa.nN × Fin pa.nN) :
    decompAtom pa a e = 0 ∨ decompAtom pa a e = 1 := by
  rcases a with p | c
  · rcases pathEnum_binary pa p e.1 e.2 with h | h <;> simp [decompAtom, h]
  · rcases cycleEnum_binary pa c e.1 e.2 with h | h <;> simp [decompAtom, h]

private lemma path_atom_structural (p : Fin (numPaths pa)) :
    StructuralFlow pa (fun i j => (pathEnum pa p i j : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    exact_mod_cast path_supplier_deg_zero_aux pa p s
  · intro t
    exact_mod_cast path_transshipment_deg_aux pa p t
  · intro b
    exact_mod_cast path_beneficiary_deg_zero_aux pa p b
  · intro i j hE
    have hle := (pathEnum_isValidPath pa p).2.1 i j
    rcases pathEnum_binary pa p i j with h | h
    · simp [h]
    · omega

private lemma cycle_atom_structural (c : Fin (numCycles pa)) :
    StructuralFlow pa (fun i j => (cycleEnum pa c i j : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    exact_mod_cast cycle_supplier_deg_zero_aux pa c s
  · intro t
    exact_mod_cast (cycleEnum_isValid pa c).2.2.2.2.1 (pa.T t)
  · intro b
    exact_mod_cast cycle_beneficiary_deg_zero_aux pa c b
  · intro i j hE
    have hle := (cycleEnum_isValid pa c).2.1 i j
    rcases cycleEnum_binary pa c i j with h | h
    · simp [h]
    · omega

private lemma decompAtom_structural
    (a : Sum (Fin (numPaths pa)) (Fin (numCycles pa))) :
    StructuralFlow pa (fun i j => decompAtom pa a (i, j)) := by
  rcases a with p | c
  · exact path_atom_structural pa p
  · exact cycle_atom_structural pa c

private lemma structural_sub_atom
    (f : Fin pa.nN × Fin pa.nN → ℝ)
    (a : Sum (Fin (numPaths pa)) (Fin (numCycles pa))) (d : ℝ)
    (hf : StructuralFlow pa (fun i j => f (i, j))) :
    StructuralFlow pa (fun i j => f (i, j) - d * decompAtom pa a (i, j)) := by
  have ha := decompAtom_structural pa a
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hf.supplier_in s, ha.supplier_in s]
    ring
  · intro t
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hf.transshipment t, ha.transshipment t]
  · intro b
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hf.beneficiary_out b, ha.beneficiary_out b]
    ring
  · intro i j hE
    rw [hf.offedge i j hE, ha.offedge i j hE]
    ring

private lemma pathEnum_has_edge (p : Fin (numPaths pa)) :
    ∃ e : Fin pa.nN × Fin pa.nN, pathEnum pa p e.1 e.2 = 1 := by
  obtain ⟨-, -, -, -, ⟨s, hout, -, -⟩, -⟩ := pathEnum_isValidPath pa p
  by_contra h
  push_neg at h
  have hz : ∀ j, pathEnum pa p (pa.S s) j = 0 := by
    intro j
    rcases pathEnum_binary pa p (pa.S s) j with h0 | h1
    · exact h0
    · exact absurd h1 (h (pa.S s, j))
  simp [hz] at hout

private lemma cycleEnum_has_edge (c : Fin (numCycles pa)) :
    ∃ e : Fin pa.nN × Fin pa.nN, cycleEnum pa c e.1 e.2 = 1 := by
  obtain ⟨-, -, -, -, -, m, verts, hm, -, -, hedge⟩ := cycleEnum_isValid pa c
  let i : Fin m := ⟨0, hm⟩
  exact ⟨(verts i.castSucc, verts i.succ), hedge _ _ |>.2 ⟨i, rfl, rfl⟩⟩

private lemma decompAtom_has_edge
    (a : Sum (Fin (numPaths pa)) (Fin (numCycles pa))) :
    ∃ e : Fin pa.nN × Fin pa.nN, decompAtom pa a e = 1 := by
  rcases a with p | c
  · simpa [decompAtom] using pathEnum_has_edge pa p
  · simpa [decompAtom] using cycleEnum_has_edge pa c

private lemma extract_decompAtom
    (f : Fin pa.nN × Fin pa.nN → ℝ)
    (hf : StructuralFlow pa (fun i j => f (i, j)))
    (hnn : ∀ e, 0 ≤ f e) (hpos : ∃ e, 0 < f e) :
    ∃ a : Sum (Fin (numPaths pa)) (Fin (numCycles pa)),
      (∀ e, decompAtom pa a e = 0 ∨ decompAtom pa a e = 1) ∧
      (∃ e, decompAtom pa a e = 1) ∧
      (∀ e, decompAtom pa a e = 1 → 0 < f e) := by
  obtain ⟨⟨i, j⟩, hij⟩ := hpos
  rcases exists_positive_enumerated_atom pa (fun i j => f (i, j)) hf
      (fun i j => hnn (i, j)) i j hij with ⟨p, hp⟩ | ⟨c, hc⟩
  · refine ⟨Sum.inl p, decompAtom_binary pa _, decompAtom_has_edge pa _, ?_⟩
    rintro ⟨u, w⟩ huw
    exact hp u w (by simpa [decompAtom] using huw)
  · refine ⟨Sum.inr c, decompAtom_binary pa _, decompAtom_has_edge pa _, ?_⟩
    rintro ⟨u, w⟩ huw
    exact hc u w (by simpa [decompAtom] using huw)

private lemma single_commodity_decomposition
    (f : Fin pa.nN → Fin pa.nN → ℝ) (hf : StructuralFlow pa f)
    (hnn : ∀ i j, 0 ≤ f i j) :
    ∃ (x : Fin (numPaths pa) → ℝ) (y : Fin (numCycles pa) → ℝ),
      (∀ p, 0 ≤ x p) ∧ (∀ c, 0 ≤ y c) ∧
      ∀ i j, f i j =
        (∑ p, (pathEnum pa p i j : ℝ) * x p) +
        (∑ c, (cycleEnum pa c i j : ℝ) * y c) := by
  classical
  let F : Fin pa.nN × Fin pa.nN → ℝ := fun e => f e.1 e.2
  obtain ⟨z, hz, hrec⟩ := finite_conic_decomposition
    (decompAtom pa)
    (fun g => StructuralFlow pa (fun i j => g (i, j)))
    (extract_decompAtom pa)
    (structural_sub_atom pa)
    F hf (fun e => hnn e.1 e.2)
  refine ⟨fun p => z (.inl p), fun c => z (.inr c), ?_, ?_, ?_⟩
  · exact fun p => hz (.inl p)
  · exact fun c => hz (.inr c)
  · intro i j
    have hr := hrec (i, j)
    rw [show (∑ a, decompAtom pa a (i, j) * z a) =
        (∑ p, (pathEnum pa p i j : ℝ) * z (.inl p)) +
        (∑ c, (cycleEnum pa c i j : ℝ) * z (.inr c)) by
      rw [Fintype.sum_sum_type]
      rfl] at hr
    exact hr

-- ============================================================================
-- § Flow decomposition and the fwd / bwd maps
-- ============================================================================

/-- **Flow decomposition (fixed-index form).** Any `a`-feasible flow decomposes,
edge by edge and for every commodity, into a nonnegative combination of the
enumerated paths and cycles. -/
lemma flow_decomposition (v : P20.a.Vars pa) (h : P20.a.Feasible pa v) :
    ∃ (x : Fin (numPaths pa) → Fin pa.nK → ℝ) (y : Fin (numCycles pa) → Fin pa.nK → ℝ),
      (∀ p k, 0 ≤ x p k) ∧ (∀ c k, 0 ≤ y c k) ∧
      (∀ i j : Fin pa.nN, ∀ k : Fin pa.nK,
        v.F i j k
          = (∑ p, (pathEnum pa p i j : ℝ) * x p k)
            + (∑ c, (cycleEnum pa c i j : ℝ) * y c k)) := by
  classical
  let D (k : Fin pa.nK) :=
    single_commodity_decomposition pa
      (fun i j => v.F i j k)
      (feasible_structural pa v h k)
      (fun i j => h.hF_nn i j k)
  refine ⟨fun p k => (D k).choose p,
    fun c k => (D k).choose_spec.choose c, ?_, ?_, ?_⟩
  · intro p k
    exact (D k).choose_spec.choose_spec.1 p
  · intro c k
    exact (D k).choose_spec.choose_spec.2.1 c
  · intro i j k
    exact (D k).choose_spec.choose_spec.2.2 i j

/-- Forward map (a → b): decompose the flow into path/cycle amounts, keep `R`. -/
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

/-- Backward map (b → a): rebuild the arc flow by summing path/cycle contributions. -/
noncomputable def bwd (vb : P20.b.Vars (paramMap pa)) : P20.a.Vars pa where
  F := fun i j k =>
    (∑ p, (pathEnum pa p i j : ℝ) * vb.x p k)
      + (∑ c, (cycleEnum pa c i j : ℝ) * vb.y c k)
  R := vb.R

/-- In the feasible case, `fwd`'s components are a valid flow decomposition. -/
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

/-- `bwd` keeps the ration `R` unchanged. -/
@[simp] lemma bwd_R (vb : P20.b.Vars (paramMap pa)) : (bwd pa vb).R = vb.R := rfl

-- ============================================================================
-- § Node-class flow facts for enumerated paths / cycles (feed `bwd_feas`)
-- ============================================================================

/-- A valid path has zero in-degree at a supplier (it can only be the source). -/
lemma path_supplier_indeg_zero (p : Fin (numPaths pa)) (s : Fin pa.nS) :
    ∑ i, pathEnum pa p i (pa.S s) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact pathEnum_zero_of_E_zero pa p i (pa.S s) (pa.hE_noinflow_S i s)

/-- A valid path has zero out-degree at a beneficiary (it can only be the sink). -/
lemma path_beneficiary_outdeg_zero (p : Fin (numPaths pa)) (b : Fin pa.nB) :
    ∑ j, pathEnum pa p (pa.B b) j = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  exact pathEnum_zero_of_E_zero pa p (pa.B b) j (pa.hE_nooutflow_B b j)

/-- A valid path has equal in- and out-degree at a transshipment node. -/
lemma path_transshipment_deg (p : Fin (numPaths pa)) (t : Fin pa.nT) :
    ∑ i, pathEnum pa p i (pa.T t) = ∑ j, pathEnum pa p (pa.T t) j := by
  obtain ⟨hbin, -, hin1, hout1, hsrc, hsink, -⟩ := pathEnum_isValidPath pa p
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

/-- A valid cycle has zero in-degree at a supplier. -/
lemma cycle_supplier_deg_zero (c : Fin (numCycles pa)) (s : Fin pa.nS) :
    ∑ i, cycleEnum pa c i (pa.S s) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact cycleEnum_zero_of_E_zero pa c i (pa.S s) (pa.hE_noinflow_S i s)

/-- A valid cycle has zero out-degree at a beneficiary. -/
lemma cycle_beneficiary_outdeg_zero (c : Fin (numCycles pa)) (b : Fin pa.nB) :
    ∑ j, cycleEnum pa c (pa.B b) j = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  exact cycleEnum_zero_of_E_zero pa c (pa.B b) j (pa.hE_nooutflow_B b j)

/-- Pointwise: a valid path carries no edge into a supplier. -/
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

/-- Off a graph edge, the reconstructed flow vanishes. -/
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
  hflow := fun t k => by
    rw [Finset.sum_congr rfl (fun i _ => bwd_E_mul pa vb i (pa.T t) k),
        Finset.sum_congr rfl (fun i _ => bwd_E_mul pa vb (pa.T t) i k),
        sum_bwd_F_in pa vb (pa.T t) k, sum_bwd_F_out pa vb (pa.T t) k]
    congr 1
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [path_transshipment_deg pa p t]
    · refine Finset.sum_congr rfl fun c _ => ?_
      obtain ⟨-, -, -, -, hcons, -⟩ := cycleEnum_isValid pa c
      rw [hcons (pa.T t)]
  hdemand := fun j k => by
    rw [Finset.sum_congr rfl (fun i _ => bwd_E_mul pa vb i (pa.B j) k),
        sum_bwd_F_in pa vb (pa.B j) k]
    have hcyc0 : (∑ c, (↑(∑ i, cycleEnum pa c i (pa.B j)) : ℝ) * vb.y c k) = 0 := by
      apply Finset.sum_eq_zero; intro c _
      obtain ⟨-, -, -, -, hcons, -⟩ := cycleEnum_isValid pa c
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

-- ============================================================================
-- § fwd_feas : a-feasible ⟹ b-feasible
-- ============================================================================

/-- `fwd` keeps the ration `R` unchanged (both branches set `R := v.R`). -/
lemma fwd_R (v : P20.a.Vars pa) : (fwd pa v).R = v.R := by
  simp only [fwd]; split <;> rfl

/-- **Forward feasibility.** An `a`-feasible solution maps to a `b`-feasible one. -/
lemma fwd_feas (v : P20.a.Vars pa) (ha : P20.a.Feasible pa v) :
    P20.b.Feasible (paramMap pa) (fwd pa v) where
  hdemand := fun j k => by
    obtain ⟨-, -, hrec⟩ := fwd_spec pa v ha
    rw [fwd_R pa v]
    have hkey :
        (∑ i, (pa.E i (pa.B j) : ℝ) * v.F i (pa.B j) k)
          = ∑ p, ((paramMap pa).e j p : ℝ) * (fwd pa v).x p k := by
      have hcast : ∀ i, (pa.E i (pa.B j) : ℝ) * v.F i (pa.B j) k
          = (bwd pa (fwd pa v)).F i (pa.B j) k := by
        intro i
        rw [hrec i (pa.B j) k]
        exact bwd_E_mul pa (fwd pa v) i (pa.B j) k
      rw [Finset.sum_congr rfl (fun i _ => hcast i), sum_bwd_F_in pa (fwd pa v) (pa.B j) k]
      have hcyc0 :
          (∑ c, (↑(∑ i, cycleEnum pa c i (pa.B j)) : ℝ) * (fwd pa v).y c k) = 0 := by
        apply Finset.sum_eq_zero; intro c _
        obtain ⟨-, -, -, -, hcons, -⟩ := cycleEnum_isValid pa c
        rw [hcons (pa.B j), cycle_beneficiary_outdeg_zero pa c j]; simp
      rw [hcyc0, add_zero]
      apply Finset.sum_congr rfl; intro p _
      have he : (paramMap pa).e j p = ∑ i, pathEnum pa p i (pa.B j) := by
        show (∑ i, pathEnum pa p i (pa.B j)) - (∑ k, pathEnum pa p (pa.B j) k)
              = ∑ i, pathEnum pa p i (pa.B j)
        rw [path_beneficiary_outdeg_zero pa p j]; ring
      rw [he]
    rw [← hkey]
    exact ha.hdemand j k
  hnutrition := fun l => by
    rw [fwd_R pa v]; exact ha.hnutrition l
  hx_nn := (fwd_spec pa v ha).1
  hy_nn := (fwd_spec pa v ha).2.1
  hR_nn := fun k => by rw [fwd_R pa v]; exact ha.hR_nn k

-- ============================================================================
-- § Objective preservation and final assembly
-- ============================================================================

/-- `a.obj` depends only on the flow `F`. -/
lemma a_obj_congr (v1 v2 : P20.a.Vars pa) (h : v1.F = v2.F) :
    P20.a.obj pa v1 = P20.a.obj pa v2 := by
  simp only [P20.a.obj, h]

/-- A valid cycle has zero out-degree at a supplier. -/
lemma cycle_supplier_outdeg_zero (c : Fin (numCycles pa)) (s : Fin pa.nS) :
    ∑ j, cycleEnum pa c (pa.S s) j = 0 := by
  obtain ⟨-, -, -, -, hcons, -⟩ := cycleEnum_isValid pa c
  rw [← hcons (pa.S s)]
  exact cycle_supplier_deg_zero pa c s

/-- Every valid path leaves exactly one supplier: total out-degree over all
suppliers is 1 (the unique source; every other supplier is off the path). -/
lemma path_supplier_total_outdeg (p : Fin (numPaths pa)) :
    ∑ s, (∑ j, pathEnum pa p (pa.S s) j) = 1 := by
  obtain ⟨hbin, -, hin1, hout1, ⟨s0, hs0out, hs0in, hs0uniq⟩, -, -⟩ :=
    pathEnum_isValidPath pa p
  have hzero : ∀ s ∈ (Finset.univ : Finset (Fin pa.nS)), s ≠ s0 →
      (∑ j, pathEnum pa p (pa.S s) j) = 0 := by
    intro s _ hsne
    by_contra hne
    have hout_nn : 0 ≤ ∑ j, pathEnum pa p (pa.S s) j :=
      Finset.sum_nonneg fun j _ => by rcases hbin (pa.S s) j with h | h <;> omega
    have hout1v : ∑ j, pathEnum pa p (pa.S s) j = 1 := by have := hout1 (pa.S s); omega
    have hin0 := path_supplier_indeg_zero pa p s
    exact hsne (pa.hS_inj (hs0uniq (pa.S s) ⟨hout1v, hin0⟩))
  rw [Finset.sum_eq_single s0 hzero (fun h => absurd (Finset.mem_univ s0) h)]
  exact hs0out

/-- Total supplier out-flow of commodity `k` in the reconstructed flow equals the
total path amount (each path leaves one supplier; cycles avoid suppliers). -/
lemma supplier_outflow (vb : P20.b.Vars (paramMap pa)) (k : Fin pa.nK) :
    (∑ s, ∑ j, (pa.E (pa.S s) j : ℝ) * (bwd pa vb).F (pa.S s) j k) = ∑ p, vb.x p k := by
  have hE : (∑ s, ∑ j, (pa.E (pa.S s) j : ℝ) * (bwd pa vb).F (pa.S s) j k)
      = ∑ s, ∑ j, (bwd pa vb).F (pa.S s) j k := by
    apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro j _
    exact bwd_E_mul pa vb (pa.S s) j k
  rw [hE]
  simp only [bwd]
  have hsplit :
      (∑ s, ∑ j, ((∑ p, (pathEnum pa p (pa.S s) j : ℝ) * vb.x p k)
          + (∑ c, (cycleEnum pa c (pa.S s) j : ℝ) * vb.y c k)))
        = (∑ s, ∑ j, ∑ p, (pathEnum pa p (pa.S s) j : ℝ) * vb.x p k)
          + (∑ s, ∑ j, ∑ c, (cycleEnum pa c (pa.S s) j : ℝ) * vb.y c k) := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro s _
    rw [← Finset.sum_add_distrib]
  rw [hsplit]
  have hcyc : (∑ s, ∑ j, ∑ c, (cycleEnum pa c (pa.S s) j : ℝ) * vb.y c k) = 0 := by
    apply Finset.sum_eq_zero; intro s _
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero; intro c _
    have hz : (∑ j, (cycleEnum pa c (pa.S s) j : ℝ)) = 0 := by
      exact_mod_cast cycle_supplier_outdeg_zero pa c s
    rw [← Finset.sum_mul, hz, zero_mul]
  have hpath : (∑ s, ∑ j, ∑ p, (pathEnum pa p (pa.S s) j : ℝ) * vb.x p k) = ∑ p, vb.x p k := by
    rw [Finset.sum_congr rfl (fun s _ => Finset.sum_comm), Finset.sum_comm]
    apply Finset.sum_congr rfl; intro p _
    have hfac : (∑ s, ∑ j, (pathEnum pa p (pa.S s) j : ℝ) * vb.x p k)
        = (∑ s, ∑ j, (pathEnum pa p (pa.S s) j : ℝ)) * vb.x p k := by
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro s _; rw [Finset.sum_mul]
    rw [hfac]
    have h1 : (∑ s, ∑ j, (pathEnum pa p (pa.S s) j : ℝ)) = 1 := by
      exact_mod_cast path_supplier_total_outdeg pa p
    rw [h1, one_mul]
  rw [hcyc, hpath, add_zero]

/-- Transportation cost of the reconstructed flow splits into path and cycle
shipping costs (`pCost` / `cCost`). -/
lemma transport_decomp (vb : P20.b.Vars (paramMap pa)) :
    (∑ i, ∑ j, ∑ k, pa.tc i j k * (bwd pa vb).F i j k)
      = (∑ p, ∑ k, (paramMap pa).pCost p k * vb.x p k)
        + (∑ c, ∑ k, (paramMap pa).cCost c k * vb.y c k) := by
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm), Finset.sum_comm,
      show (∑ p, ∑ k, (paramMap pa).pCost p k * vb.x p k)
          = ∑ k, ∑ p, (paramMap pa).pCost p k * vb.x p k from Finset.sum_comm,
      show (∑ c, ∑ k, (paramMap pa).cCost c k * vb.y c k)
          = ∑ k, ∑ c, (paramMap pa).cCost c k * vb.y c k from Finset.sum_comm,
      ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  show ∑ i, ∑ j, pa.tc i j k
        * ((∑ p, (pathEnum pa p i j : ℝ) * vb.x p k)
            + (∑ c, (cycleEnum pa c i j : ℝ) * vb.y c k))
      = (∑ p, (∑ i, ∑ j, pa.tc i j k * (pathEnum pa p i j : ℝ)) * vb.x p k)
        + (∑ c, (∑ i, ∑ j, pa.tc i j k * (cycleEnum pa c i j : ℝ)) * vb.y c k)
  have hP : (∑ i, ∑ j, ∑ p, pa.tc i j k * (pathEnum pa p i j : ℝ) * vb.x p k)
      = ∑ p, (∑ i, ∑ j, pa.tc i j k * (pathEnum pa p i j : ℝ)) * vb.x p k := by
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm), Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
  have hC : (∑ i, ∑ j, ∑ c, pa.tc i j k * (cycleEnum pa c i j : ℝ) * vb.y c k)
      = ∑ c, (∑ i, ∑ j, pa.tc i j k * (cycleEnum pa c i j : ℝ)) * vb.y c k := by
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm), Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
  calc
    ∑ i, ∑ j, pa.tc i j k
          * ((∑ p, (pathEnum pa p i j : ℝ) * vb.x p k)
              + (∑ c, (cycleEnum pa c i j : ℝ) * vb.y c k))
        = ∑ i, ∑ j, ((∑ p, pa.tc i j k * (pathEnum pa p i j : ℝ) * vb.x p k)
              + (∑ c, pa.tc i j k * (cycleEnum pa c i j : ℝ) * vb.y c k)) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [mul_add, Finset.mul_sum, Finset.mul_sum]
          congr 1
          · exact Finset.sum_congr rfl fun p _ => by ring
          · exact Finset.sum_congr rfl fun c _ => by ring
      _ = (∑ i, ∑ j, ∑ p, pa.tc i j k * (pathEnum pa p i j : ℝ) * vb.x p k)
          + (∑ i, ∑ j, ∑ c, pa.tc i j k * (cycleEnum pa c i j : ℝ) * vb.y c k) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_add_distrib]
      _ = _ := by rw [hP, hC]

/-- **Objective correspondence.** `b.obj` on a solution equals `a.obj` on its
reconstruction. This gives `bwd_obj` directly and `fwd_obj` via `fwd_spec`. -/
lemma obj_corr (vb : P20.b.Vars (paramMap pa)) :
    P20.b.obj (paramMap pa) vb = P20.a.obj pa (bwd pa vb) := by
  have hproc :
      (∑ k, pa.pc k * (∑ s, ∑ j, (pa.E (pa.S s) j : ℝ) * (bwd pa vb).F (pa.S s) j k))
        = ∑ k, (paramMap pa).q k * (∑ p, vb.x p k) := by
    apply Finset.sum_congr rfl; intro k _
    rw [supplier_outflow pa vb k]; rfl
  simp only [P20.b.obj, P20.a.obj]
  rw [← transport_decomp pa vb, hproc]
  ring

/-- **Backward objective.** -/
lemma bwd_obj (vb : P20.b.Vars (paramMap pa)) :
    P20.b.obj (paramMap pa) vb = P20.a.obj pa (bwd pa vb) := obj_corr pa vb

/-- **Forward objective.** -/
lemma fwd_obj (v : P20.a.Vars pa) (ha : P20.a.Feasible pa v) :
    P20.b.obj (paramMap pa) (fwd pa v) = P20.a.obj pa v := by
  rw [obj_corr pa (fwd pa v)]
  apply a_obj_congr
  obtain ⟨-, -, hrec⟩ := fwd_spec pa v ha
  funext i j k
  exact (hrec i j k).symm

/-- **Inverse consistency.** On feasible points `bwd` undoes `fwd`: the ration is
carried through untouched, and re-aggregating the path/cycle amounts produced by
the decomposition rebuilds the original arc flow. -/
lemma bwd_fwd (v : P20.a.Vars pa) (ha : P20.a.Feasible pa v) :
    bwd pa (fwd pa v) = v := by
  obtain ⟨-, -, hrec⟩ := fwd_spec pa v ha
  have hF : (bwd pa (fwd pa v)).F = v.F := by
    funext i j k
    exact (hrec i j k).symm
  have hR : (bwd pa (fwd pa v)).R = v.R := by
    show (fwd pa v).R = v.R
    simp only [fwd, dif_pos ha]
  calc bwd pa (fwd pa v)
      = ⟨(bwd pa (fwd pa v)).F, (bwd pa (fwd pa v)).R⟩ := rfl
    _ = ⟨v.F, v.R⟩ := by rw [hF, hR]
    _ = v := rfl

/-- **The reformulation.** `P20.a` (arc flow) ⇄ `P20.b` (path + cycle), with the
identity objective map. -/
noncomputable def reformulation :
    MILPReformulation P20.a.formulation P20.b.formulation where
  paramMap := paramMap
  fwd := fwd
  bwd := bwd
  fwd_feas := fwd_feas
  bwd_feas := bwd_feas
  objMap := id
  objMap_mono := strictMono_id
  fwd_obj := fwd_obj
  bwd_obj := fun _ vb _ => bwd_obj _ vb

end P20.AB
