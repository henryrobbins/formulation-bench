import Common
import problems.p14.formulations.a.Formulation
import problems.p14.formulations.b.Formulation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

open BigOperators Finset

namespace P14

-- ============================================================================
-- § Parameter Mapping
-- ============================================================================

private def paramMap (p : P14.a.Params) : P14.b.Params :=
  { nS          := p.nS
    nH          := p.nH
    numDC       := p.numDC
    T           := p.T
    T_limit     := p.T_limit
    hnS         := p.hnS
    hnH         := p.hnH
    hT_nn       := p.hT_nn
    hT_limit_nn := p.hT_limit_nn
    hnumDC_le   := p.hnumDC_le }

-- ============================================================================
-- § Shared Helpers
-- ============================================================================

-- Both directions hinge on the same fact: an assignment that vanishes wherever
-- `delta` is 0 is unchanged by multiplication with `delta`. In A that fact is
-- the constraint `hinfeas`; in B it is forced by `htime` (see `b_infeas`).

private lemma delta_mul {p : P14.a.Params} {y : Fin p.nS → Fin p.nH → ℤ}
    (hinf : ∀ i j, p.delta i j = 0 → y i j = 0) (i : Fin p.nS) (j : Fin p.nH) :
    p.delta i j * y i j = y i j := by
  rcases p.hdelta_bin i j with hd0 | hd1
  · rw [hd0, hinf i j hd0]; ring
  · rw [hd1]; ring

private lemma obj_eq {p : P14.a.Params} {y : Fin p.nS → Fin p.nH → ℤ}
    (hinf : ∀ i j, p.delta i j = 0 → y i j = 0) :
    ∑ i : Fin p.nS, ∑ j : Fin p.nH, (y i j : ℝ) * p.T i j
      = ∑ i : Fin p.nS, ∑ j : Fin p.nH,
          (p.delta i j : ℝ) * (y i j : ℝ) * p.T i j := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rcases p.hdelta_bin i j with hd0 | hd1
  · rw [hd0, hinf i j hd0]; push_cast; ring
  · rw [hd1]; push_cast; ring

-- ============================================================================
-- § Forward Mapping and Feasibility
-- ============================================================================

private def fwd (p : P14.a.Params) (v : P14.a.Vars p) : P14.b.Vars (paramMap p) :=
  { x := v.x
    y := v.y }

private lemma fwd_feas (p : P14.a.Params) (v : P14.a.Vars p)
    (h : P14.a.Feasible p v) :
    P14.b.Feasible (paramMap p) (fwd p v) := by
  have hx_nn : ∀ i : Fin p.nS, 0 ≤ v.x i := fun i => by
    rcases h.hx_bin i with h0 | h1 <;> omega
  constructor
  · -- hselect
    exact h.hselect
  · -- hactive: A's `∑ delta * y ≤ x * ∑ delta` weakens to the big-M bound,
    -- since `∑ delta ≤ nH` and `x ≥ 0`
    intro i
    show ∑ j : Fin p.nH, v.y i j ≤ v.x i * (p.nH : ℤ)
    have hdsum : ∑ j : Fin p.nH, p.delta i j ≤ (p.nH : ℤ) := by
      calc ∑ j : Fin p.nH, p.delta i j
          ≤ ∑ _j : Fin p.nH, (1 : ℤ) :=
            Finset.sum_le_sum fun j _ => by
              rcases p.hdelta_bin i j with hd0 | hd1 <;> omega
        _ = (p.nH : ℤ) := by simp
    calc ∑ j : Fin p.nH, v.y i j
        = ∑ j : Fin p.nH, p.delta i j * v.y i j :=
          Finset.sum_congr rfl fun j _ => (delta_mul h.hinfeas i j).symm
      _ ≤ v.x i * ∑ j : Fin p.nH, p.delta i j := h.hactive i
      _ ≤ v.x i * (p.nH : ℤ) := mul_le_mul_of_nonneg_left hdsum (hx_nn i)
  · -- hassign: ∑ y = 1
    intro j
    show ∑ i : Fin p.nS, v.y i j = 1
    calc ∑ i : Fin p.nS, v.y i j
        = ∑ i : Fin p.nS, p.delta i j * v.y i j :=
          Finset.sum_congr rfl fun i _ => (delta_mul h.hinfeas i j).symm
      _ = 1 := h.hassign j
  · -- htime: T i j * y ≤ T_limit
    intro i j
    show p.T i j * (v.y i j : ℝ) ≤ p.T_limit
    rcases h.hy_bin i j with hy0 | hy1
    · rw [hy0]; push_cast; simp [p.hT_limit_nn]
    · rw [hy1]; push_cast
      -- y = 1 rules out delta = 0 (that would force y = 0 by hinfeas)
      rcases p.hdelta_bin i j with hd0 | hd1
      · exfalso
        have := h.hinfeas i j hd0
        omega
      · rw [mul_one]; exact (p.hdelta_def i j).1.mp hd1
  · -- hx_bin
    exact h.hx_bin
  · -- hy_bin
    exact h.hy_bin

-- ============================================================================
-- § Backward Mapping and Feasibility
-- ============================================================================

private def bwd (p : P14.a.Params) (v : P14.b.Vars (paramMap p)) : P14.a.Vars p :=
  { x := v.x
    y := v.y }

-- B has no `delta`; the travel-time constraint plays its role: assigning a
-- hospital beyond the limit (`delta = 0`) would violate `htime`.
private lemma b_infeas {p : P14.a.Params} {v : P14.b.Vars (paramMap p)}
    (h : P14.b.Feasible (paramMap p) v) :
    ∀ i j, p.delta i j = 0 → v.y i j = 0 := by
  intro i j hd0
  rcases h.hy_bin i j with hy0 | hy1
  · exact hy0
  · exfalso
    have hT_gt : p.T_limit < p.T i j := (p.hdelta_def i j).2.mp hd0
    have htime := h.htime i j
    rw [hy1] at htime
    simp only [paramMap] at htime
    push_cast at htime
    linarith

private lemma bwd_feas (p : P14.a.Params) (v : P14.b.Vars (paramMap p))
    (h : P14.b.Feasible (paramMap p) v) :
    P14.a.Feasible p (bwd p v) := by
  have hinf := b_infeas h
  constructor
  · -- hselect
    exact h.hselect
  · -- hactive: ∑ delta * y = ∑ y, which x = 0 forces to 0 and x = 1 bounds by
    -- ∑ delta (pointwise y ≤ delta)
    intro i
    simp only [bwd]
    have hrw : ∑ j : Fin p.nH, p.delta i j * v.y i j = ∑ j : Fin p.nH, v.y i j :=
      Finset.sum_congr rfl fun j _ => delta_mul hinf i j
    rw [hrw]
    rcases h.hx_bin i with hx0 | hx1
    · have hact := h.hactive i
      rw [hx0] at hact ⊢
      simpa using hact
    · rw [hx1, one_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      rcases p.hdelta_bin i j with hd0 | hd1
      · rw [hd0, hinf i j hd0]
      · rw [hd1]
        rcases h.hy_bin i j with hy0 | hy1 <;> omega
  · -- hassign: ∑ delta * y = 1
    intro j
    simp only [bwd]
    have hrw : ∑ i : Fin p.nS, p.delta i j * v.y i j = ∑ i : Fin p.nS, v.y i j :=
      Finset.sum_congr rfl fun i _ => delta_mul hinf i j
    rw [hrw]
    exact h.hassign j
  · -- hinfeas
    intro i j hd0
    simp only [bwd]
    exact hinf i j hd0
  · -- hx_bin
    intro i
    simp only [bwd]
    exact h.hx_bin i
  · -- hy_bin
    intro i j
    simp only [bwd]
    exact h.hy_bin i j

-- ============================================================================
-- § Objective Mapping
-- ============================================================================

private lemma fwd_obj (p : P14.a.Params) (v : P14.a.Vars p)
    (h : P14.a.Feasible p v) :
    (P14.b.formulation).obj (paramMap p) (fwd p v) = P14.a.formulation.obj p v := by
  show P14.b.obj (paramMap p) (fwd p v) = P14.a.obj p v
  unfold P14.b.obj P14.a.obj
  exact obj_eq h.hinfeas

private lemma bwd_obj (p : P14.a.Params) (v : P14.b.Vars (paramMap p))
    (h : P14.b.Feasible (paramMap p) v) :
    (P14.b.formulation).obj (paramMap p) v = P14.a.formulation.obj p (bwd p v) := by
  show P14.b.obj (paramMap p) v = P14.a.obj p (bwd p v)
  unfold P14.b.obj P14.a.obj
  exact obj_eq (b_infeas h)

-- ============================================================================
-- § Reformulation Structure
-- ============================================================================

def aBReformulation : MILPReformulation P14.a.formulation P14.b.formulation where
  paramMap    := paramMap
  fwd         := fwd
  bwd         := bwd
  fwd_feas    := fwd_feas
  bwd_feas    := bwd_feas
  bwd_fwd     := fun _ _ _ => rfl
  objMap      := id
  objMap_mono := strictMono_id
  fwd_obj p v h := fwd_obj p v h
  bwd_obj p v h := bwd_obj p v h

end P14
