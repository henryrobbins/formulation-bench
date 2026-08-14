import Common
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic

open BigOperators Finset

namespace P13.b

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
  y : (k : Fin p.nK) → Fin (p.nP k) → Fin p.nA → Fin p.nT → ℤ
    -- 1 if flight pl of class k is at location a at time t
  z : (k : Fin p.nK) → Fin (p.nP k) → Fin p.nA → Fin p.nA → Fin p.nT → ℤ
    -- 1 if flight pl of class k moves from a at time t to a' at time t+1

structure Feasible (p : Params) (v : Vars p) : Prop where
  -- Each flight is at exactly one location at each time
  hassign : ∀ (k : Fin p.nK) (pl : Fin (p.nP k)) (t : Fin p.nT),
    ∑ a : Fin p.nA, v.y k pl a t = 1
  -- Respect location capacity at each time, counting the flights of all classes
  hcap : ∀ (a : Fin p.nA) (t : Fin p.nT),
    (∑ k : Fin p.nK, ∑ pl : Fin (p.nP k), (v.y k pl a t : ℝ)) ≤ (p.cap a t : ℝ)
  -- Flow conservation: one-step transitions (for t > 0)
  hflow : ∀ (k : Fin p.nK) (pl : Fin (p.nP k)) (a : Fin p.nA) (t : Fin p.nT), ∀ ht : 0 < t.val,
    v.y k pl a t =
      v.y k pl a ⟨t.val - 1, by omega⟩ +
      ∑ a' : Fin p.nA, v.z k pl a' a ⟨t.val - 1, by
        omega⟩ -
      ∑ a' : Fin p.nA, v.z k pl a a' ⟨t.val - 1, by
        omega⟩
  -- Movements only between adjacent locations
  hadj : ∀ (k : Fin p.nK) (pl : Fin (p.nP k)) (a a' : Fin p.nA) (t : Fin p.nT),
    v.z k pl a a' t ≤ p.adj a a'
  -- No movements out of the final time period
  hno_depart_last : ∀ (k : Fin p.nK) (pl : Fin (p.nP k)) (a a' : Fin p.nA) (t : Fin p.nT),
    t.val + 1 = p.nT → v.z k pl a a' t = 0
  -- Movements at time t require presence at time t (depart only from where you are)
  hstay_nn : ∀ (k : Fin p.nK) (pl : Fin (p.nP k)) (a : Fin p.nA) (t : Fin p.nT),
    (∑ a' : Fin p.nA, v.z k pl a a' t) ≤ v.y k pl a t
  -- y_{k,pl,a,t} ∈ {0,1}
  hy_bin : ∀ (k : Fin p.nK) (pl : Fin (p.nP k)) (a : Fin p.nA) (t : Fin p.nT),
    v.y k pl a t = 0 ∨ v.y k pl a t = 1
  -- z_{k,pl,a,a',t} ∈ {0,1}
  hz_bin : ∀ (k : Fin p.nK) (pl : Fin (p.nP k)) (a a' : Fin p.nA) (t : Fin p.nT),
    v.z k pl a a' t = 0 ∨ v.z k pl a a' t = 1

-- Maximize total reward for visiting locations
def obj (p : Params) (v : Vars p) : ℝ :=
  -(∑ k : Fin p.nK, ∑ pl : Fin (p.nP k), ∑ a : Fin p.nA, ∑ t : Fin p.nT,
    p.r k a t * (v.y k pl a t : ℝ))

def formulation : MILPFormulation where
  Params   := Params
  Vars     := Vars
  feasible := Feasible
  obj      := obj

end P13.b
