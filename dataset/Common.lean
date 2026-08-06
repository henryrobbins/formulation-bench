import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Set.Card

structure MILPFormulation where
  Params   : Type
  Vars     : Params → Type
  feasible : (p : Params) → Vars p → Prop
  obj      : (p : Params) → Vars p → ℝ

namespace MILPFormulation

/-- The set of objective values attained on the feasible set at `p`. -/
def values (F : MILPFormulation) (p : F.Params) : Set ℝ :=
  F.obj p '' {x | F.feasible p x}

/-- The feasible points at `p` attaining objective value `v`. -/
def levelSet (F : MILPFormulation) (p : F.Params) (v : ℝ) : Set (F.Vars p) :=
  {x | F.feasible p x ∧ F.obj p x = v}

end MILPFormulation

structure MILPReformulation (F G : MILPFormulation) where
  paramMap    : F.Params → G.Params
  fwd         : (p : F.Params) → F.Vars p → G.Vars (paramMap p)
  bwd         : (p : F.Params) → G.Vars (paramMap p) → F.Vars p
  fwd_feas    : ∀ p x, F.feasible p x → G.feasible (paramMap p) (fwd p x)
  bwd_feas    : ∀ p x', G.feasible (paramMap p) x' → F.feasible p (bwd p x')
  bwd_fwd     : ∀ p x, F.feasible p x → bwd p (fwd p x) = x
  objMap      : ℝ → ℝ
  objMap_mono : StrictMono objMap
  fwd_obj     : ∀ p x, F.feasible p x →
                  G.obj (paramMap p) (fwd p x) = objMap (F.obj p x)
  bwd_obj     : ∀ p x', G.feasible (paramMap p) x' →
                  G.obj (paramMap p) x' = objMap (F.obj p (bwd p x'))

namespace MILPReformulation

variable {F G : MILPFormulation}

/-- **Level-set injection (i).** `objMap` maps the objective values attained by
`F` at `p` onto those attained by `G` at `paramMap p`. -/
theorem objMap_image_values (Φ : MILPReformulation F G) (p : F.Params) :
    Φ.objMap '' F.values p = G.values (Φ.paramMap p) := by
  ext v'
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨Φ.fwd p x, Φ.fwd_feas p x hx, Φ.fwd_obj p x hx⟩
  · rintro ⟨x', hx', rfl⟩
    exact ⟨F.obj p (Φ.bwd p x'), ⟨Φ.bwd p x', Φ.bwd_feas p x' hx', rfl⟩,
      (Φ.bwd_obj p x' hx').symm⟩

/-- **Level-set injection (ii), image.** `fwd` sends the level set of `F` at
value `v` into the level set of `G` at value `objMap v`. -/
theorem fwd_mapsTo_levelSet (Φ : MILPReformulation F G) (p : F.Params) (v : ℝ) :
    Set.MapsTo (Φ.fwd p) (F.levelSet p v) (G.levelSet (Φ.paramMap p) (Φ.objMap v)) := by
  rintro x ⟨hx, rfl⟩
  exact ⟨Φ.fwd_feas p x hx, Φ.fwd_obj p x hx⟩

/-- **Level-set injection (ii), injectivity.** `fwd` is injective on each level
set of `F`. -/
theorem fwd_injOn_levelSet (Φ : MILPReformulation F G) (p : F.Params) (v : ℝ) :
    Set.InjOn (Φ.fwd p) (F.levelSet p v) := by
  intro x₁ h₁ x₂ h₂ h
  rw [← Φ.bwd_fwd p x₁ h₁.1, ← Φ.bwd_fwd p x₂ h₂.1, h]

/-- **Feasible-set injection.** `fwd` restricts to an injection of the feasible
set of `F` at `p` into the feasible set of `G` at `paramMap p`. Corollary of
`fwd_injOn_levelSet`: two feasible points with the same image share an
objective value, so they lie in a common level set. -/
theorem fwd_injOn (Φ : MILPReformulation F G) (p : F.Params) :
    Set.InjOn (Φ.fwd p) {x | F.feasible p x} := by
  intro x₁ h₁ x₂ h₂ h
  have hv : F.obj p x₁ = F.obj p x₂ :=
    Φ.objMap_mono.injective <| by rw [← Φ.fwd_obj p x₁ h₁, ← Φ.fwd_obj p x₂ h₂, h]
  exact Φ.fwd_injOn_levelSet p (F.obj p x₁) ⟨h₁, rfl⟩ ⟨h₂, hv.symm⟩ h

/-- **Objective-level bijection.** `objMap` is a bijection from the objective
values attained by `F` at `p` onto those attained by `G` at `paramMap p`. -/
theorem objMap_bijOn (Φ : MILPReformulation F G) (p : F.Params) :
    Set.BijOn Φ.objMap (F.values p) (G.values (Φ.paramMap p)) := by
  refine ⟨fun v hv => ?_, Φ.objMap_mono.injective.injOn, ?_⟩
  · rw [← Φ.objMap_image_values p]
    exact ⟨v, hv, rfl⟩
  · rw [← Φ.objMap_image_values p]
    exact Set.surjOn_image _ _

/-- **Least value preservation.** Being an order isomorphism onto the attained
values of `G`, `objMap` carries a least attained value of `F` to the least
attained value of `G`. -/
theorem isLeast_objMap (Φ : MILPReformulation F G) (p : F.Params) {v : ℝ}
    (hv : IsLeast (F.values p) v) : IsLeast (G.values (Φ.paramMap p)) (Φ.objMap v) := by
  constructor
  · rw [← Φ.objMap_image_values p]
    exact ⟨v, hv.1, rfl⟩
  · rintro v' hv'
    rw [← Φ.objMap_image_values p] at hv'
    obtain ⟨w, hw, rfl⟩ := hv'
    exact Φ.objMap_mono.monotone (hv.2 hw)

/-- **Feasible-set cardinality disproof.** No reformulation `F → G` can exist
once `G`'s feasible set is *strictly smaller* than `F`'s at a mapped parameter.

Concretely: suppose `F.feasible p` is finite, there is an injection `g` of the
feasible points of `G` (at `Φ.paramMap p`) back into those of `F`, and some
`F`-feasible point `w` lies outside the image of `g`. Then `Φ.fwd` injects
`F`-feasibles into `G`-feasibles while `g` injects them back missing `w`, forcing
`|F| ≤ |G| < |F|` — a contradiction. This is the constructive contrapositive of
`fwd_injOn`, used when adding a cut removes a feasible point (so `g` is the
inclusion of the augmented feasible set). -/
theorem false_of_feasible_embeds_missing (Φ : MILPReformulation F G)
    (p : F.Params) (hfin : Set.Finite {x | F.feasible p x})
    (g : G.Vars (Φ.paramMap p) → F.Vars p)
    (hg_maps : Set.MapsTo g {x | G.feasible (Φ.paramMap p) x} {x | F.feasible p x})
    (hg_inj : Set.InjOn g {x | G.feasible (Φ.paramMap p) x})
    (w : F.Vars p) (hw : F.feasible p w)
    (hw_missing : w ∉ g '' {x | G.feasible (Φ.paramMap p) x}) : False := by
  set Fs : Set (F.Vars p) := {x | F.feasible p x}
  set Gs : Set (G.Vars (Φ.paramMap p)) := {x | G.feasible (Φ.paramMap p) x}
  have hfwd_maps : Set.MapsTo (Φ.fwd p) Fs Gs := fun x hx => Φ.fwd_feas p x hx
  have hfwd_inj : Set.InjOn (Φ.fwd p) Fs := Φ.fwd_injOn p
  have hGfin : Set.Finite Gs :=
    (Set.finite_image_iff hg_inj).mp (hfin.subset hg_maps.image_subset)
  have h1 : Set.ncard Fs ≤ Set.ncard Gs :=
    calc Set.ncard Fs
        = Set.ncard (Φ.fwd p '' Fs) := (hfwd_inj.ncard_image).symm
      _ ≤ Set.ncard Gs := Set.ncard_le_ncard hfwd_maps.image_subset hGfin
  have h2 : Set.ncard (g '' Gs) = Set.ncard Gs := hg_inj.ncard_image
  have h3 : g '' Gs ⊂ Fs :=
    (Set.ssubset_iff_of_subset hg_maps.image_subset).mpr ⟨w, hw, hw_missing⟩
  have h4 : Set.ncard (g '' Gs) < Set.ncard Fs := Set.ncard_lt_ncard h3 hfin
  omega

end MILPReformulation
