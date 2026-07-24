import Common
import problems.p5.formulations.a.Formulation
import problems.p5.formulations.c.Formulation

/-!
# `c` is not a reformulation of `a`

Formulation `c` has four decimal digits, hence at most `10⁴` feasible points on
any instance. Formulation `a` has an instance with `10⁴ + 1` distinct feasible
points obtained by varying only the subsoil count. Its feasible set cannot
inject into any `c`-instance, regardless of the parameter mapping.
-/

namespace P5

private def pLarge : P5.a.Params where
  WaterSubsoil := 0
  WaterTopsoil := 0
  MaxTotalBags := 10000
  MinTopsoilBags := 0
  MaxTopsoilProportion := 1
  hWaterSubsoil_nn := le_refl 0
  hWaterTopsoil_nn := le_refl 0
  hMaxTotalBags_nn := by norm_num
  hMinTopsoilBags_nn := le_refl 0
  hMaxTopsoilProportion_nn := zero_le_one

private def pt (n : Fin 10001) : P5.a.Vars pLarge :=
  ⟨n.val, 0⟩

private lemma pt_feasible (n : Fin 10001) : P5.a.Feasible pLarge (pt n) where
  htotal := by
    simp [pLarge, pt]
    have hn : n.val ≤ 10000 := by omega
    exact_mod_cast hn
  hmin_top := by norm_num [pLarge, pt]
  hprop := by norm_num [pLarge, pt]
  hss_nn := by simp [pt]
  hts_nn := le_refl 0

private abbrev Digit := Set.Icc (0 : ℤ) 9

theorem aCNotReformulation :
    IsEmpty (MILPReformulation P5.a.formulation P5.c.formulation) := by
  refine ⟨fun Φ => ?_⟩
  let code : Fin 10001 → (((Digit × Digit) × Digit) × Digit) :=
    fun n =>
      let v := Φ.fwd pLarge (pt n)
      let h := Φ.fwd_feas pLarge (pt n) (pt_feasible n)
      (((⟨v.h_0, h.hh0_nn, h.hh0_hi⟩, ⟨v.h_1, h.hh1_nn, h.hh1_hi⟩),
        ⟨v.d_0, h.hd0_nn, h.hd0_hi⟩), ⟨v.d_1, h.hd1_nn, h.hd1_hi⟩)
  have hcode : Function.Injective code := by
    intro m n h
    have hh0 := congrArg (fun z => z.1.1.1.val) h
    have hh1 := congrArg (fun z => z.1.1.2.val) h
    have hd0 := congrArg (fun z => z.1.2.val) h
    have hd1 := congrArg (fun z => z.2.val) h
    simp only [code] at hh0 hh1 hd0 hd1
    have hfwd : Φ.fwd pLarge (pt m) = Φ.fwd pLarge (pt n) := by
      cases hm : Φ.fwd pLarge (pt m)
      cases hn : Φ.fwd pLarge (pt n)
      simp_all
    have hpt := Φ.fwd_injOn pLarge (pt_feasible m) (pt_feasible n) hfwd
    have hval := congrArg P5.a.Vars.SubsoilBags hpt
    apply Fin.ext
    change (m.val : ℤ) = (n.val : ℤ) at hval
    exact_mod_cast hval
  have hcard := Fintype.card_le_of_injective code hcode
  norm_num [Digit, Fintype.card_prod, Fintype.card_Icc, Int.toNat] at hcard

end P5
