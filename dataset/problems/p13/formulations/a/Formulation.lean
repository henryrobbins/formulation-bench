import Common
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic

open BigOperators Finset

namespace P13.a

structure Params where
  nK : ℕ  -- number of plane classes
  nP : Fin nK → ℕ  -- number of flights of each class
  nA : ℕ  -- number of locations
  nT : ℕ  -- number of time periods
  adj : Fin nA → Fin nA → ℤ  -- adjacency matrix (1 if a adjacent to a', 0 otherwise)
  r : Fin nK → Fin nA → Fin nT → ℝ  -- reward for a class k flight at location a at time t
  cap : Fin nA → Fin nT → ℤ  -- capacity of location a at time t
  -- Assumptions
  hadj_bin : ∀ a a', adj a a' = 0 ∨ adj a a' = 1
  -- Implicit Assumptions
  hnK : NeZero nK
  hnA : NeZero nA
  hnT : NeZero nT
  hadj_self : ∀ a, adj a a = 1
  hcap_nn : ∀ a t, 0 ≤ cap a t

structure Vars (p : Params) where
  n : Fin p.nK → Fin p.nA → Fin p.nT → ℤ  -- number of class k flights at location a at time t
  f : Fin p.nK → Fin p.nA → Fin p.nA → Fin p.nT → ℤ
    -- number of class k flights moving from a at time t to a' at time t+1

structure Feasible (p : Params) (v : Vars p) : Prop where
  -- All flights of every class are accounted for at every time period
  hcount : ∀ (k : Fin p.nK) (t : Fin p.nT), ∑ a : Fin p.nA, v.n k a t = (p.nP k : ℤ)
  -- Flights of all classes at a location do not exceed the location capacity
  hcap : ∀ (a : Fin p.nA) (t : Fin p.nT),
    (∑ k : Fin p.nK, (v.n k a t : ℝ)) ≤ (p.cap a t : ℝ)
  -- Flow conservation: one-step transitions (for t > 0)
  hflow : ∀ (k : Fin p.nK) (a : Fin p.nA) (t : Fin p.nT), ∀ ht : 0 < t.val,
    v.n k a t =
      v.n k a ⟨t.val - 1, by omega⟩ +
      ∑ a' : Fin p.nA, v.f k a' a ⟨t.val - 1, by
        have _ : t.val < p.nT := t.isLt
        omega⟩ -
      ∑ a' : Fin p.nA, v.f k a a' ⟨t.val - 1, by
        have _ : t.val < p.nT := t.isLt
        omega⟩
  -- Movements only between adjacent locations
  hadj : ∀ (k : Fin p.nK) (a a' : Fin p.nA) (t : Fin p.nT),
    v.f k a a' t ≤ (p.nP k : ℤ) * p.adj a a'
  -- No movements out of the final time period
  hno_depart_last : ∀ (k : Fin p.nK) (a a' : Fin p.nA) (t : Fin p.nT),
    t.val + 1 = p.nT → v.f k a a' t = 0
  -- Aggregate departures at time t do not exceed presence at time t (stay-flow ≥ 0)
  hstay_nn : ∀ (k : Fin p.nK) (a : Fin p.nA) (t : Fin p.nT),
    (∑ a' : Fin p.nA, v.f k a a' t) ≤ v.n k a t
  hn_nn : ∀ (k : Fin p.nK) (a : Fin p.nA) (t : Fin p.nT), 0 ≤ v.n k a t
  hf_nn : ∀ (k : Fin p.nK) (a a' : Fin p.nA) (t : Fin p.nT), 0 ≤ v.f k a a' t

-- Maximize total reward for all flights across all classes, locations, and time periods
def obj (p : Params) (v : Vars p) : ℝ :=
  -(∑ k : Fin p.nK, ∑ a : Fin p.nA, ∑ t : Fin p.nT, p.r k a t * (v.n k a t : ℝ))

def formulation : MILPFormulation where
  Params   := Params
  Vars     := Vars
  feasible := Feasible
  obj      := obj

end P13.a
