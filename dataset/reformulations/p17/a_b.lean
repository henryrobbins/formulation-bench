import Common
import problems.p17.formulations.a.Formulation
import problems.p17.formulations.b.Formulation

/-!
# `b` is not a reformulation of `a`

Formulation `a` permits fractional extraction for pure-ore blocks, so it has an
instance with infinitely many feasible points. Every feasible point of
formulation `b` is binary, hence every `b`-instance has only finitely many
feasible points. No feasible-set injection can exist, regardless of the
parameter mapping.
-/

namespace P17

private def pFree : P17.a.Params where
  n := 1
  T := 1
  c := fun _ _ => 0
  g := fun _ => 1
  O := fun _ => 0
  W := fun _ => 0
  G_min := 0
  G_max := 0
  PC_min := 0
  PC_max := 0
  MC_min := 0
  MC_max := 0
  P := fun _ _ => 0
  hP_bin := fun _ _ => Or.inl rfl
  hn := ⟨by omega⟩
  hT := ⟨by omega⟩
  hc_nn := fun _ _ => le_refl 0
  hg_nn := fun _ => by norm_num
  hg_le_one := fun _ => by norm_num
  hO_nn := fun _ => le_refl 0
  hW_nn := fun _ => le_refl 0

private noncomputable def pt (k : ℕ) : P17.a.Vars pFree :=
  ⟨fun _ _ => 1 / ((k : ℝ) + 1)⟩

private lemma pt_feasible (k : ℕ) : P17.a.Feasible pFree (pt k) where
  hgrade_hi := by simp [pFree, pt]
  hgrade_lo := by simp [pFree, pt]
  honce := by
    intro i
    simp [pFree, pt]
    exact inv_le_one_of_one_le₀ (by norm_num)
  hproc_hi := by simp [pFree, pt]
  hproc_lo := by simp [pFree, pt]
  hmine_hi := by simp [pFree, pt]
  hmine_lo := by simp [pFree, pt]
  hprec := by simp [pFree]
  hx_bin_I0 := by simp [pFree]
  hx_lo_I1 := by
    intro i t _
    simp [pt]
    positivity
  hx_hi_I1 := by
    intro i t _
    simp [pt]
    exact inv_le_one_of_one_le₀ (by norm_num)

private lemma pt_injective : Function.Injective pt := by
  intro k l h
  let i : Fin pFree.n := ⟨0, by simp [pFree]⟩
  let t : Fin pFree.T := ⟨0, by simp [pFree]⟩
  have h' := congrFun (congrFun (congrArg P17.a.Vars.x h) i) t
  simp only [pt] at h'
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  have hl : (l : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hk, hl] at h'
  have hkl : (k : ℝ) = l := by linarith
  exact_mod_cast hkl

private lemma b_feasible_finite (q : P17.b.Params) :
    Set.Finite {v : P17.b.Vars q | P17.b.Feasible q v} := by
  classical
  let digit : Set ℤ := {0, 1}
  let periodFns : Set (Fin q.T → ℤ) := {f | ∀ t, f t ∈ digit}
  let blockFns : Set (Fin q.n → Fin q.T → ℤ) := {f | ∀ i, f i ∈ periodFns}
  let encode : P17.b.Vars q → (Fin q.n → Fin q.T → ℤ) := fun v => v.x
  have hdigit : digit.Finite := by
    simp [digit]
  have hperiod : periodFns.Finite := by
    simpa [periodFns] using Set.Finite.pi' (fun _ : Fin q.T => hdigit)
  have hblock : blockFns.Finite := by
    simpa [blockFns] using Set.Finite.pi' (fun _ : Fin q.n => hperiod)
  refine (hblock.subset ?_).of_finite_image (f := encode) ?_
  · rintro x ⟨v, hv, hx⟩
    subst x
    intro i t
    simpa [digit] using hv.hx_bin i t
  · intro v _ w _ h
    cases v
    cases w
    simpa [encode] using h

theorem aBNotReformulation :
    IsEmpty (MILPReformulation P17.a.formulation P17.b.formulation) := by
  refine ⟨fun Φ => ?_⟩
  have htarget := b_feasible_finite (Φ.paramMap pFree)
  have himage : Set.Finite
      (Φ.fwd pFree '' {v : P17.a.Vars pFree | P17.a.Feasible pFree v}) :=
    htarget.subset (by
      rintro x ⟨v, hv, hx⟩
      subst x
      exact Φ.fwd_feas pFree v hv)
  have hsource : Set.Finite {v : P17.a.Vars pFree | P17.a.Feasible pFree v} :=
    himage.of_finite_image (Φ.fwd_injOn pFree)
  have hrange : (Set.range pt).Infinite := Set.infinite_range_of_injective pt_injective
  exact hrange (hsource.subset (by
    rintro x ⟨k, hk⟩
    subst x
    exact pt_feasible k))

end P17
