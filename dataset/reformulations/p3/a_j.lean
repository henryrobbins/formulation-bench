import Common
import problems.p3.formulations.a.Formulation
import problems.p3.formulations.j.Formulation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open BigOperators Finset

namespace P3

private def active (p : P3.a.Params) (i : Fin p.NumBeakers) : Prop :=
  0 < p.FlourUsagePerBeaker i ∨
    0 < p.SpecialLiquidUsagePerBeaker i ∨
    0 < p.WasteProducedPerBeaker i

private noncomputable instance activeDecidable (p : P3.a.Params)
    (i : Fin p.NumBeakers) : Decidable (active p i) :=
  Classical.propDecidable _

private lemma not_active_coefficients {p : P3.a.Params} {i : Fin p.NumBeakers}
    (hi : ¬active p i) :
    p.FlourUsagePerBeaker i = 0 ∧
      p.SpecialLiquidUsagePerBeaker i = 0 ∧
      p.WasteProducedPerBeaker i = 0 := by
  simp only [active, not_or] at hi
  constructor
  · exact le_antisymm (not_lt.mp hi.1) (p.hFlour_nn i)
  constructor
  · exact le_antisymm (not_lt.mp hi.2.1) (p.hLiquid_nn i)
  · exact le_antisymm (not_lt.mp hi.2.2) (p.hWaste_nn i)

private noncomputable def coordBound (p : P3.a.Params)
    (i : Fin p.NumBeakers) : ℕ :=
  if 0 < p.FlourUsagePerBeaker i then
    Nat.find (exists_nat_gt (p.FlourAvailable / p.FlourUsagePerBeaker i))
  else if 0 < p.SpecialLiquidUsagePerBeaker i then
    Nat.find
      (exists_nat_gt
        (p.SpecialLiquidAvailable / p.SpecialLiquidUsagePerBeaker i))
  else if 0 < p.WasteProducedPerBeaker i then
    Nat.find
      (exists_nat_gt (p.MaxWasteAllowed / p.WasteProducedPerBeaker i))
  else 1

private abbrev Candidate (p : P3.a.Params) :=
  (i : Fin p.NumBeakers) → Fin (coordBound p i)

private noncomputable instance candidateFintype (p : P3.a.Params) :
    Fintype (Candidate p) :=
  by
    classical
    exact Pi.instFintype

private noncomputable def decode (p : P3.a.Params) (c : Candidate p) :
    P3.a.Vars p :=
  { NumBeakersUsed := fun i => (c i : ℕ) }

private abbrev BoundedFeas (p : P3.a.Params) :=
  {c : Candidate p // P3.a.Feasible p (decode p c)}

private noncomputable instance boundedFeasFintype (p : P3.a.Params) :
    Fintype (BoundedFeas p) :=
  by
    classical
    exact Subtype.fintype _

private abbrev TargetIdx (p : P3.a.Params) :=
  Unit ⊕ (Fin p.NumBeakers ⊕ BoundedFeas p)

private noncomputable instance targetIdxFintype (p : P3.a.Params) :
    Fintype (TargetIdx p) :=
  by
    classical
    infer_instance

private noncomputable def idxEquiv (p : P3.a.Params) :
    TargetIdx p ≃ Fin (Fintype.card (TargetIdx p)) :=
  Fintype.equivFin _

private lemma target_card_pos (p : P3.a.Params) :
    0 < Fintype.card (TargetIdx p) := by
  rw [Fintype.card_pos_iff]
  exact ⟨Sum.inl ()⟩

private noncomputable def rawV (p : P3.a.Params) (k : TargetIdx p) : ℝ :=
  match k with
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl i) => if active p i then 1 else 0
  | Sum.inr (Sum.inr _) => 1

private noncomputable def targetV (p : P3.a.Params)
    (k : Fin (Fintype.card (TargetIdx p))) : ℝ :=
  rawV p ((idxEquiv p).symm k)

private noncomputable def coreValue (p : P3.a.Params) (c : BoundedFeas p) : ℝ :=
  ∑ i : Fin p.NumBeakers,
    p.SlimeProducedPerBeaker i * ((decode p c.1).NumBeakersUsed i : ℝ)

private noncomputable def rawX (p : P3.a.Params) (k : TargetIdx p) : ℝ :=
  match k with
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl i) =>
      if active p i then 0 else p.SlimeProducedPerBeaker i
  | Sum.inr (Sum.inr c) => coreValue p c

private noncomputable def targetX (p : P3.a.Params)
    (k : Fin (Fintype.card (TargetIdx p))) : ℝ :=
  rawX p ((idxEquiv p).symm k)

private noncomputable def paramMap (p : P3.a.Params) : P3.j.Params :=
  by
    classical
    exact
      { N := Fintype.card (TargetIdx p)
        C := fun _ => 0
        E := 0
        X := targetX p
        T := fun _ => 0
        D := 0
        V := targetV p
        Z := if ∃ v : P3.a.Vars p, P3.a.Feasible p v then 1 else -1
        hN := ⟨Nat.ne_of_gt (target_card_pos p)⟩
        hC_nn := fun _ => le_rfl
        hX_nn := by
          intro k
          change 0 ≤ rawX p ((idxEquiv p).symm k)
          generalize (idxEquiv p).symm k = q
          rcases q with _ | i
          · simp [rawX]
          rcases i with i | c
          · by_cases hi : active p i
            · simp [rawX, hi]
            · simpa [rawX, hi] using p.hSlime_nn i
          · simp only [rawX, coreValue]
            apply sum_nonneg
            intro i _
            apply mul_nonneg (p.hSlime_nn i)
            exact_mod_cast c.2.hNumBeakersUsed_nn i
        hT_nn := fun _ => le_rfl
        hV_nn := by
          intro k
          change 0 ≤ rawV p ((idxEquiv p).symm k)
          generalize (idxEquiv p).symm k = q
          rcases q with _ | i
          · simp [rawV]
          rcases i with i | c
          · by_cases hi : active p i <;> simp [rawV, hi]
          · simp [rawV] }

private lemma coord_lt_bound (p : P3.a.Params) (v : P3.a.Vars p)
    (h : P3.a.Feasible p v) (i : Fin p.NumBeakers) (hi : active p i) :
    (v.NumBeakersUsed i).toNat < coordBound p i := by
  have hxnn : 0 ≤ v.NumBeakersUsed i := h.hNumBeakersUsed_nn i
  have cast_nn : 0 ≤ (v.NumBeakersUsed i : ℝ) := by exact_mod_cast hxnn
  by_cases hf : 0 < p.FlourUsagePerBeaker i
  · have hterm :
        p.FlourUsagePerBeaker i * (v.NumBeakersUsed i : ℝ) ≤
          ∑ j : Fin p.NumBeakers,
            p.FlourUsagePerBeaker j * (v.NumBeakersUsed j : ℝ) := by
      simpa using
        (Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin p.NumBeakers)))
          (f := fun j =>
            p.FlourUsagePerBeaker j * (v.NumBeakersUsed j : ℝ))
          (fun j _ => mul_nonneg (p.hFlour_nn j)
            (by exact_mod_cast h.hNumBeakersUsed_nn j))
          (Finset.mem_univ i))
    have hxdiv :
        (v.NumBeakersUsed i : ℝ) ≤
          p.FlourAvailable / p.FlourUsagePerBeaker i := by
      apply (le_div_iff₀ hf).2
      simpa [mul_comm] using hterm.trans h.hflour
    have hlt :
        (v.NumBeakersUsed i : ℝ) <
          (coordBound p i : ℕ) := by
      refine hxdiv.trans_lt ?_
      simpa [coordBound, hf] using
        (Nat.find_spec
          (exists_nat_gt
            (p.FlourAvailable / p.FlourUsagePerBeaker i)))
    rw [Int.toNat_lt hxnn]
    exact_mod_cast hlt
  · by_cases hl : 0 < p.SpecialLiquidUsagePerBeaker i
    · have hterm :
          p.SpecialLiquidUsagePerBeaker i * (v.NumBeakersUsed i : ℝ) ≤
            ∑ j : Fin p.NumBeakers,
              p.SpecialLiquidUsagePerBeaker j *
                (v.NumBeakersUsed j : ℝ) := by
        simpa using
          (Finset.single_le_sum
            (s := (Finset.univ : Finset (Fin p.NumBeakers)))
            (f := fun j =>
              p.SpecialLiquidUsagePerBeaker j *
                (v.NumBeakersUsed j : ℝ))
            (fun j _ => mul_nonneg (p.hLiquid_nn j)
              (by exact_mod_cast h.hNumBeakersUsed_nn j))
            (Finset.mem_univ i))
      have hxdiv :
          (v.NumBeakersUsed i : ℝ) ≤
            p.SpecialLiquidAvailable /
              p.SpecialLiquidUsagePerBeaker i := by
        apply (le_div_iff₀ hl).2
        simpa [mul_comm] using hterm.trans h.hliquid
      have hlt :
          (v.NumBeakersUsed i : ℝ) <
            (coordBound p i : ℕ) := by
        refine hxdiv.trans_lt ?_
        simpa [coordBound, hf, hl] using
          (Nat.find_spec
            (exists_nat_gt
              (p.SpecialLiquidAvailable /
                p.SpecialLiquidUsagePerBeaker i)))
      rw [Int.toNat_lt hxnn]
      exact_mod_cast hlt
    · have hw : 0 < p.WasteProducedPerBeaker i := by
        rcases hi with hi | hi | hi
        · exact absurd hi hf
        · exact absurd hi hl
        · exact hi
      have hterm :
          p.WasteProducedPerBeaker i * (v.NumBeakersUsed i : ℝ) ≤
            ∑ j : Fin p.NumBeakers,
              p.WasteProducedPerBeaker j * (v.NumBeakersUsed j : ℝ) := by
        simpa using
          (Finset.single_le_sum
            (s := (Finset.univ : Finset (Fin p.NumBeakers)))
            (f := fun j =>
              p.WasteProducedPerBeaker j * (v.NumBeakersUsed j : ℝ))
            (fun j _ => mul_nonneg (p.hWaste_nn j)
              (by exact_mod_cast h.hNumBeakersUsed_nn j))
            (Finset.mem_univ i))
      have hxdiv :
          (v.NumBeakersUsed i : ℝ) ≤
            p.MaxWasteAllowed / p.WasteProducedPerBeaker i := by
        apply (le_div_iff₀ hw).2
        simpa [mul_comm] using hterm.trans h.hwaste
      have hlt :
          (v.NumBeakersUsed i : ℝ) <
            (coordBound p i : ℕ) := by
        refine hxdiv.trans_lt ?_
        simpa [coordBound, hf, hl, hw] using
          (Nat.find_spec
            (exists_nat_gt
              (p.MaxWasteAllowed / p.WasteProducedPerBeaker i)))
      rw [Int.toNat_lt hxnn]
      exact_mod_cast hlt

private noncomputable def project (p : P3.a.Params) (v : P3.a.Vars p)
    (h : P3.a.Feasible p v) : Candidate p :=
  by
    classical
    exact fun i =>
      if hi : active p i then
        ⟨(v.NumBeakersUsed i).toNat, coord_lt_bound p v h i hi⟩
      else
        ⟨0, by simp [coordBound, not_active_coefficients hi]⟩

private lemma decode_project (p : P3.a.Params) (v : P3.a.Vars p)
    (h : P3.a.Feasible p v) (i : Fin p.NumBeakers) :
    (decode p (project p v h)).NumBeakersUsed i =
      if active p i then v.NumBeakersUsed i else 0 := by
  classical
  by_cases hi : active p i
  · simp [decode, project, hi, Int.toNat_of_nonneg (h.hNumBeakersUsed_nn i)]
  · simp [decode, project, hi]

private lemma project_feasible (p : P3.a.Params) (v : P3.a.Vars p)
    (h : P3.a.Feasible p v) :
    P3.a.Feasible p (decode p (project p v h)) := by
  have hflour :
      (∑ i : Fin p.NumBeakers,
        p.FlourUsagePerBeaker i *
          ((decode p (project p v h)).NumBeakersUsed i : ℝ)) =
        ∑ i : Fin p.NumBeakers,
          p.FlourUsagePerBeaker i * (v.NumBeakersUsed i : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [decode_project p v h i]
    by_cases hi : active p i
    · simp [hi]
    · rw [(not_active_coefficients hi).1]
      simp
  have hliquid :
      (∑ i : Fin p.NumBeakers,
        p.SpecialLiquidUsagePerBeaker i *
          ((decode p (project p v h)).NumBeakersUsed i : ℝ)) =
        ∑ i : Fin p.NumBeakers,
          p.SpecialLiquidUsagePerBeaker i * (v.NumBeakersUsed i : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [decode_project p v h i]
    by_cases hi : active p i
    · simp [hi]
    · rw [(not_active_coefficients hi).2.1]
      simp
  have hwaste :
      (∑ i : Fin p.NumBeakers,
        p.WasteProducedPerBeaker i *
          ((decode p (project p v h)).NumBeakersUsed i : ℝ)) =
        ∑ i : Fin p.NumBeakers,
          p.WasteProducedPerBeaker i * (v.NumBeakersUsed i : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [decode_project p v h i]
    by_cases hi : active p i
    · simp [hi]
    · rw [(not_active_coefficients hi).2.2]
      simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hflour] using h.hflour
  · simpa [hliquid] using h.hliquid
  · simpa [hwaste] using h.hwaste
  · intro i
    change 0 ≤ ((project p v h i : ℕ) : ℤ)
    exact_mod_cast Nat.zero_le (project p v h i : ℕ)

private noncomputable def corePart (p : P3.a.Params) (v : P3.a.Vars p)
    (h : P3.a.Feasible p v) : BoundedFeas p :=
  ⟨project p v h, project_feasible p v h⟩

private lemma decode_eq_zero_of_not_active (p : P3.a.Params) (c : Candidate p)
    (i : Fin p.NumBeakers) (hi : ¬active p i) :
    (decode p c).NumBeakersUsed i = 0 := by
  have hc : (c i : ℕ) = 0 := by
    have hlt : (c i : ℕ) < 1 := by
      simpa [coordBound, not_active_coefficients hi] using (c i).isLt
    omega
  change ((c i : ℕ) : ℤ) = 0
  simp [hc]

private noncomputable def targetAt (p : P3.a.Params)
    (v : P3.j.Vars (paramMap p)) (k : TargetIdx p) : ℤ :=
  v.n (idxEquiv p k)

private lemma sum_target {M : Type*} [AddCommMonoid M] (p : P3.a.Params)
    (g : Fin (Fintype.card (TargetIdx p)) → M) :
    (∑ k, g k) = ∑ k : TargetIdx p, g (idxEquiv p k) :=
  (idxEquiv p).sum_comp g |>.symm

private noncomputable def fwd (p : P3.a.Params) (v : P3.a.Vars p) :
    P3.j.Vars (paramMap p) :=
  by
    classical
    exact
      { n := fun k =>
          match (idxEquiv p).symm k with
          | Sum.inl _ => 0
          | Sum.inr (Sum.inl i) =>
              if active p i then 0 else v.NumBeakersUsed i
          | Sum.inr (Sum.inr c) =>
              if hv : P3.a.Feasible p v then
                if c = corePart p v hv then 1 else 0
              else 0 }

private lemma fwd_feas (p : P3.a.Params) (v : P3.a.Vars p)
    (h : P3.a.Feasible p v) :
    P3.j.Feasible (paramMap p) (fwd p v) := by
  classical
  constructor
  · change
      (∑ k, targetV p k * ((fwd p v).n k : ℝ)) ≤
        (if ∃ w : P3.a.Vars p, P3.a.Feasible p w then 1 else -1)
    rw [sum_target]
    simp only [Fintype.sum_sum_type]
    have hex : ∃ w : P3.a.Vars p, P3.a.Feasible p w := ⟨v, h⟩
    simp [targetV, rawV, fwd, h, hex]
    apply Finset.sum_nonpos
    intro i _
    by_cases hi : active p i <;> simp [hi]
  · intro k
    generalize hk : (idxEquiv p).symm k = q
    rcases q with _ | q
    · simp [fwd, hk]
    rcases q with i | c
    · by_cases hi : active p i
      · simp [fwd, hk, hi]
      · simpa [fwd, hk, hi] using h.hNumBeakersUsed_nn i
    · simp only [fwd, hk]
      split_ifs <;> omega

private noncomputable def bwd (p : P3.a.Params)
    (v : P3.j.Vars (paramMap p)) : P3.a.Vars p :=
  by
    classical
    exact
      { NumBeakersUsed := fun i =>
          if hi : active p i then
            ∑ c : BoundedFeas p, targetAt p v (Sum.inr (Sum.inr c)) *
              (decode p c.1).NumBeakersUsed i
          else targetAt p v (Sum.inr (Sum.inl i)) }

private lemma targetAt_nonneg (p : P3.a.Params)
    (v : P3.j.Vars (paramMap p)) (h : P3.j.Feasible (paramMap p) v)
    (k : TargetIdx p) : 0 ≤ targetAt p v k := by
  exact h.hn_nn (idxEquiv p k)

private lemma target_budget (p : P3.a.Params)
    (v : P3.j.Vars (paramMap p)) (h : P3.j.Feasible (paramMap p) v) :
    (targetAt p v (Sum.inl ()) : ℝ) +
        ((∑ i : Fin p.NumBeakers,
            if active p i then
              (targetAt p v (Sum.inr (Sum.inl i)) : ℝ)
            else 0) +
          ∑ c : BoundedFeas p,
            (targetAt p v (Sum.inr (Sum.inr c)) : ℝ)) ≤
      (paramMap p).Z := by
  classical
  have hb := h.hliquid
  change (∑ k, targetV p k * (v.n k : ℝ)) ≤ (paramMap p).Z at hb
  rw [sum_target] at hb
  simpa [targetV, rawV, targetAt, Fintype.sum_sum_type] using hb

private lemma source_nonempty (p : P3.a.Params)
    (v : P3.j.Vars (paramMap p)) (h : P3.j.Feasible (paramMap p) v) :
    ∃ w : P3.a.Vars p, P3.a.Feasible p w := by
  classical
  by_contra hn
  push_neg at hn
  have hb := target_budget p v h
  simp [paramMap, hn] at hb
  have hu : 0 ≤ (targetAt p v (Sum.inl ()) : ℝ) := by
    exact_mod_cast targetAt_nonneg p v h (Sum.inl ())
  have hs :
      0 ≤ ∑ c : BoundedFeas p,
        (targetAt p v (Sum.inr (Sum.inr c)) : ℝ) := by
    apply Finset.sum_nonneg
    intro c _
    exact_mod_cast targetAt_nonneg p v h (Sum.inr (Sum.inr c))
  have hd :
      0 ≤ ∑ i : Fin p.NumBeakers,
        if active p i then
          (targetAt p v (Sum.inr (Sum.inl i)) : ℝ)
        else 0 := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact_mod_cast targetAt_nonneg p v h (Sum.inr (Sum.inl i))
    · exact le_rfl
  linarith

private lemma selector_sum_le_one (p : P3.a.Params)
    (v : P3.j.Vars (paramMap p)) (h : P3.j.Feasible (paramMap p) v) :
    (∑ c : BoundedFeas p,
      (targetAt p v (Sum.inr (Sum.inr c)) : ℝ)) ≤ 1 := by
  have hb := target_budget p v h
  have hex := source_nonempty p v h
  classical
  simp [paramMap, hex] at hb
  have hu : 0 ≤ (targetAt p v (Sum.inl ()) : ℝ) := by
    exact_mod_cast targetAt_nonneg p v h (Sum.inl ())
  have hd :
      0 ≤ ∑ i : Fin p.NumBeakers,
        if active p i then
          (targetAt p v (Sum.inr (Sum.inl i)) : ℝ)
        else 0 := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact_mod_cast targetAt_nonneg p v h (Sum.inr (Sum.inl i))
    · exact le_rfl
  linarith

private lemma weighted_constraint (p : P3.a.Params)
    (v : P3.j.Vars (paramMap p)) (h : P3.j.Feasible (paramMap p) v)
    (coeff : Fin p.NumBeakers → ℝ) (cap : ℝ)
    (hcoeff_nn : ∀ i, 0 ≤ coeff i)
    (hcoeff_free : ∀ i, ¬active p i → coeff i = 0)
    (hcore : ∀ c : BoundedFeas p,
      (∑ i : Fin p.NumBeakers,
        coeff i * ((decode p c.1).NumBeakersUsed i : ℝ)) ≤ cap) :
    (∑ i : Fin p.NumBeakers,
      coeff i * ((bwd p v).NumBeakersUsed i : ℝ)) ≤ cap := by
  classical
  obtain ⟨w, hw⟩ := source_nonempty p v h
  have hcap_nn : 0 ≤ cap := by
    have hsum_nn :
        0 ≤ ∑ i : Fin p.NumBeakers,
          coeff i *
            ((decode p (corePart p w hw).1).NumBeakersUsed i : ℝ) := by
      apply Finset.sum_nonneg
      intro i _
      apply mul_nonneg (hcoeff_nn i)
      exact_mod_cast
        (corePart p w hw).2.hNumBeakersUsed_nn i
    exact hsum_nn.trans (hcore (corePart p w hw))
  calc
    (∑ i : Fin p.NumBeakers,
        coeff i * ((bwd p v).NumBeakersUsed i : ℝ)) =
        ∑ i : Fin p.NumBeakers,
          coeff i *
            (∑ c : BoundedFeas p,
              (targetAt p v (Sum.inr (Sum.inr c)) : ℝ) *
                ((decode p c.1).NumBeakersUsed i : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : active p i
      · simp only [bwd, hi]
        push_cast
        rfl
      · rw [hcoeff_free i hi]
        simp
    _ = ∑ c : BoundedFeas p,
          (targetAt p v (Sum.inr (Sum.inr c)) : ℝ) *
            (∑ i : Fin p.NumBeakers,
              coeff i * ((decode p c.1).NumBeakersUsed i : ℝ)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ c : BoundedFeas p,
          (targetAt p v (Sum.inr (Sum.inr c)) : ℝ) * cap := by
      apply Finset.sum_le_sum
      intro c _
      apply mul_le_mul_of_nonneg_left (hcore c)
      exact_mod_cast targetAt_nonneg p v h (Sum.inr (Sum.inr c))
    _ = (∑ c : BoundedFeas p,
          (targetAt p v (Sum.inr (Sum.inr c)) : ℝ)) * cap := by
      rw [Finset.sum_mul]
    _ ≤ 1 * cap := by
      apply mul_le_mul_of_nonneg_right (selector_sum_le_one p v h) hcap_nn
    _ = cap := one_mul cap

private lemma bwd_feas (p : P3.a.Params)
    (v : P3.j.Vars (paramMap p)) (h : P3.j.Feasible (paramMap p) v) :
    P3.a.Feasible p (bwd p v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact weighted_constraint p v h p.FlourUsagePerBeaker p.FlourAvailable
      p.hFlour_nn (fun i hi => (not_active_coefficients hi).1)
      (fun c => c.2.hflour)
  · exact weighted_constraint p v h p.SpecialLiquidUsagePerBeaker
      p.SpecialLiquidAvailable p.hLiquid_nn
      (fun i hi => (not_active_coefficients hi).2.1)
      (fun c => c.2.hliquid)
  · exact weighted_constraint p v h p.WasteProducedPerBeaker p.MaxWasteAllowed
      p.hWaste_nn (fun i hi => (not_active_coefficients hi).2.2)
      (fun c => c.2.hwaste)
  · intro i
    classical
    by_cases hi : active p i
    · simp only [bwd, hi]
      apply Finset.sum_nonneg
      intro c _
      apply mul_nonneg (targetAt_nonneg p v h _)
      change 0 ≤ (((c.1 i : Fin (coordBound p i)) : ℕ) : ℤ)
      exact_mod_cast Nat.zero_le (c.1 i : ℕ)
    · simpa [bwd, hi] using
        targetAt_nonneg p v h (Sum.inr (Sum.inl i))

private lemma bwd_fwd (p : P3.a.Params) (v : P3.a.Vars p)
    (h : P3.a.Feasible p v) :
    bwd p (fwd p v) = v := by
  cases v with
  | mk x =>
    unfold bwd
    congr 1
    funext i
    classical
    by_cases hi : active p i
    · simp [hi, targetAt, fwd, h, corePart, decode_project]
    · simp [hi, targetAt, fwd]

private lemma fwd_obj (p : P3.a.Params) (v : P3.a.Vars p)
    (h : P3.a.Feasible p v) :
    P3.j.obj (paramMap p) (fwd p v) = P3.a.obj p v := by
  classical
  unfold P3.j.obj P3.a.obj
  congr 1
  change
    (∑ k, targetX p k * ((fwd p v).n k : ℝ)) =
      ∑ i, p.SlimeProducedPerBeaker i * (v.NumBeakersUsed i : ℝ)
  rw [sum_target]
  simp only [Fintype.sum_sum_type]
  simp [targetX, rawX, fwd, h, coreValue, corePart, decode_project,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : active p i <;> simp [hi]

private lemma bwd_obj (p : P3.a.Params)
    (v : P3.j.Vars (paramMap p)) (_h : P3.j.Feasible (paramMap p) v) :
    P3.j.obj (paramMap p) v = P3.a.obj p (bwd p v) := by
  classical
  unfold P3.j.obj P3.a.obj
  congr 1
  change
    (∑ k, targetX p k * (v.n k : ℝ)) =
      ∑ i, p.SlimeProducedPerBeaker i *
        ((bwd p v).NumBeakersUsed i : ℝ)
  rw [sum_target]
  simp only [Fintype.sum_sum_type]
  simp only [targetX, rawX, targetAt, bwd, coreValue,
    Equiv.symm_apply_apply, zero_mul]
  simp only [Finset.sum_const_zero, zero_add]
  have hcore :
      (∑ c : BoundedFeas p,
        (∑ i : Fin p.NumBeakers,
          p.SlimeProducedPerBeaker i *
            ((decode p c.1).NumBeakersUsed i : ℝ)) *
          (targetAt p v (Sum.inr (Sum.inr c)) : ℝ)) =
        ∑ i : Fin p.NumBeakers,
          if active p i then
            p.SlimeProducedPerBeaker i *
              (∑ c : BoundedFeas p,
                (targetAt p v (Sum.inr (Sum.inr c)) : ℝ) *
                  ((decode p c.1).NumBeakersUsed i : ℝ))
          else 0 := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : active p i
    · simp only [hi, ↓reduceIte]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    · simp only [hi, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro c _
      rw [decode_eq_zero_of_not_active p c.1 i hi]
      simp
  simp only [targetAt] at hcore
  rw [hcore]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : active p i <;> simp [hi]

noncomputable def aJReformulation :
    MILPReformulation P3.a.formulation P3.j.formulation where
  paramMap := paramMap
  fwd := fwd
  bwd := bwd
  fwd_feas := fwd_feas
  bwd_feas := bwd_feas
  bwd_fwd := bwd_fwd
  objMap := id
  objMap_mono := strictMono_id
  fwd_obj := fwd_obj
  bwd_obj := bwd_obj

end P3
