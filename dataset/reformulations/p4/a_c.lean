import Common
import problems.p4.formulations.a.Formulation
import problems.p4.formulations.c.Formulation

/-!
# `c` is not a reformulation of `a`

All four decision digits in formulation `c` lie between `0` and `9`, so every
`c`-instance has finitely many feasible points. Formulation `a` has an instance
with infinitely many feasible car counts. No feasible-set injection can exist,
regardless of the parameter mapping.
-/

namespace P4

private def pFree : P4.a.Params where
  CarCapacity := 0
  CarPollution := 0
  BusCapacity := 0
  BusPollution := 0
  MinEmployeesToTransport := 0
  MaxBuses := 0
  hCarCapacity_nn := le_refl 0
  hCarPollution_nn := le_refl 0
  hBusCapacity_nn := le_refl 0
  hBusPollution_nn := le_refl 0
  hMinEmployeesToTransport_nn := le_refl 0
  hMaxBuses_nn := le_refl 0

private def pt (n : ℕ) : P4.a.Vars pFree :=
  ⟨n, 0⟩

private lemma pt_feasible (n : ℕ) : P4.a.Feasible pFree (pt n) where
  htransport := by norm_num [pFree, pt]
  hmaxbus := by norm_num [pFree, pt]
  hcars_nn := by simp [pt]
  hbus_nn := le_refl 0

private lemma pt_injective : Function.Injective pt := by
  intro m n h
  have h' := congrArg P4.a.Vars.xCars h
  simpa [pt] using h'

private lemma c_feasible_finite (q : P4.c.Params) :
    Set.Finite {v : P4.c.Vars q | P4.c.Feasible q v} := by
  classical
  let digit : Set ℤ := Set.Icc 0 9
  let codes : Set (((ℤ × ℤ) × ℤ) × ℤ) :=
    ((digit ×ˢ digit) ×ˢ digit) ×ˢ digit
  let encode : P4.c.Vars q → ((ℤ × ℤ) × ℤ) × ℤ :=
    fun v => (((v.m_0, v.m_1), v.h_0), v.h_1)
  have hdigit : digit.Finite := by
    exact Set.finite_Icc (0 : ℤ) 9
  have hcodes : codes.Finite := by
    simpa [codes] using ((hdigit.prod hdigit).prod hdigit).prod hdigit
  refine (hcodes.subset ?_).of_finite_image (f := encode) ?_
  · rintro x ⟨v, hv, hx⟩
    subst x
    exact ⟨⟨⟨⟨hv.hm0_nn, hv.hm0_hi⟩, ⟨hv.hm1_nn, hv.hm1_hi⟩⟩,
      ⟨hv.hh0_nn, hv.hh0_hi⟩⟩, ⟨hv.hh1_nn, hv.hh1_hi⟩⟩
  · intro v _ w _ h
    cases v
    cases w
    simp only [encode, Prod.mk.injEq] at h
    rcases h with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    subst h1
    subst h2
    subst h3
    subst h4
    rfl

theorem aCNotReformulation :
    IsEmpty (MILPReformulation P4.a.formulation P4.c.formulation) := by
  refine ⟨fun Φ => ?_⟩
  have htarget := c_feasible_finite (Φ.paramMap pFree)
  have himage : Set.Finite
      (Φ.fwd pFree '' {v : P4.a.Vars pFree | P4.a.Feasible pFree v}) :=
    htarget.subset (by
      rintro x ⟨v, hv, hx⟩
      subst x
      exact Φ.fwd_feas pFree v hv)
  have hsource : Set.Finite {v : P4.a.Vars pFree | P4.a.Feasible pFree v} :=
    himage.of_finite_image (Φ.fwd_injOn pFree)
  have hrange : (Set.range pt).Infinite := Set.infinite_range_of_injective pt_injective
  exact hrange (hsource.subset (by
    rintro x ⟨n, hn⟩
    subst x
    exact pt_feasible n))

end P4
