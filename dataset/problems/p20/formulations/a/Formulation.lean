import Common
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic

open BigOperators Finset

namespace P20.a

structure Params where
  nN : ℕ  -- total number of nodes
  nS : ℕ  -- number of supplier nodes
  nT : ℕ  -- number of transshipment nodes
  nB : ℕ  -- number of beneficiary camps
  nK : ℕ  -- number of commodities
  nL : ℕ  -- number of nutrients
  S : Fin nS → Fin nN  -- maps supplier index to node index
  T : Fin nT → Fin nN  -- maps transshipment index to node index
  B : Fin nB → Fin nN  -- maps beneficiary camp index to node index
  E : Fin nN → Fin nN → ℤ  -- adjacency matrix (1 if edge exists, 0 otherwise)
  dem : Fin nB → ℝ  -- number of beneficiaries at each beneficiary camp
  cap : Fin nT → ℤ  -- throughput capacity in kg of each transshipment node
  pc : Fin nK → ℝ  -- procurement cost per kg of each commodity
  tc : Fin nN → Fin nN → Fin nK → ℝ  -- transportation cost per kg along each arc per commodity
  nutreq : Fin nL → ℝ  -- per-person nutritional requirement for each nutrient
  nutval : Fin nK → Fin nL → ℝ  -- nutritional value per kg of each commodity for each nutrient
  -- Assumptions
  hE_bin : ∀ i j : Fin nN, E i j = 0 ∨ E i j = 1
  -- The supplier, transshipment, and beneficiary node-class maps partition N
  hSTB_partition : ∀ v : Fin nN,
    (∃ s : Fin nS, S s = v) ∨ (∃ t : Fin nT, T t = v) ∨ (∃ b : Fin nB, B b = v)
  hSTB_disj_ST : ∀ (s : Fin nS) (t : Fin nT), S s ≠ T t
  hSTB_disj_SB : ∀ (s : Fin nS) (b : Fin nB), S s ≠ B b
  hSTB_disj_TB : ∀ (t : Fin nT) (b : Fin nB), T t ≠ B b
  hS_inj : Function.Injective S
  hT_inj : Function.Injective T
  hB_inj : Function.Injective B
  -- Supplier nodes have no incoming arcs
  hE_noinflow_S : ∀ i : Fin nN, ∀ s : Fin nS, E i (S s) = 0
  -- Beneficiary camps have no outgoing arcs
  hE_nooutflow_B : ∀ b : Fin nB, ∀ j : Fin nN, E (B b) j = 0
  -- Implicit Assumptions
  hnN : NeZero nN
  hnS : NeZero nS
  hnT : NeZero nT
  hnB : NeZero nB
  hnK : NeZero nK
  hnL : NeZero nL
  hdem_nn : ∀ j : Fin nB, 0 ≤ dem j
  hcap_nn : ∀ t : Fin nT, 0 ≤ cap t
  hpc_nn : ∀ k : Fin nK, 0 ≤ pc k
  htc_nn : ∀ i j : Fin nN, ∀ k : Fin nK, 0 ≤ tc i j k
  hnutreq_nn : ∀ l : Fin nL, 0 ≤ nutreq l
  hnutval_nn : ∀ k : Fin nK, ∀ l : Fin nL, 0 ≤ nutval k l

structure Vars (p : Params) where
  F : Fin p.nN → Fin p.nN → Fin p.nK → ℤ  -- amount of commodity k sent from node i to node j (kg)
  R : Fin p.nK → ℝ  -- ration size per person of each commodity (kg)

structure Feasible (p : Params) (v : Vars p) : Prop where
  -- Flow conservation at transshipment nodes for each commodity (no storage)
  hflow : ∀ j : Fin p.nT, ∀ k : Fin p.nK,
    ∑ i : Fin p.nN, p.E i (p.T j) * v.F i (p.T j) k =
    ∑ i : Fin p.nN, p.E (p.T j) i * v.F (p.T j) i k
  -- Total throughput at each transshipment node, measured on inflow, is within capacity
  hcap : ∀ t : Fin p.nT,
    ∑ k : Fin p.nK, ∑ i : Fin p.nN, p.E i (p.T t) * v.F i (p.T t) k ≤ p.cap t
  -- Beneficiary camps receive at least their ration demand
  hdemand : ∀ j : Fin p.nB, ∀ k : Fin p.nK,
    p.dem j * v.R k ≤ ∑ i : Fin p.nN, (p.E i (p.B j) : ℝ) * (v.F i (p.B j) k : ℝ)
  -- Rations satisfy all nutritional requirements
  hnutrition : ∀ l : Fin p.nL,
    p.nutreq l ≤ ∑ k : Fin p.nK, p.nutval k l * v.R k
  -- Flow is supported on graph edges (no flow on non-edges)
  hF_offedge : ∀ i j : Fin p.nN, ∀ k : Fin p.nK,
    p.E i j = 0 → v.F i j k = 0
  -- [Implicit Constraints]
  hF_nn : ∀ i j : Fin p.nN, ∀ k : Fin p.nK, 0 ≤ v.F i j k
  hR_nn : ∀ k : Fin p.nK, 0 ≤ v.R k

-- Minimize total procurement and transportation cost.
-- Procurement cost is charged on the outflow of each commodity leaving supplier nodes.
def obj (p : Params) (v : Vars p) : ℝ :=
  (∑ k : Fin p.nK, p.pc k *
    (∑ s : Fin p.nS, ∑ j : Fin p.nN, (p.E (p.S s) j : ℝ) * (v.F (p.S s) j k : ℝ)))
    + ∑ i : Fin p.nN, ∑ j : Fin p.nN, ∑ k : Fin p.nK, p.tc i j k * (v.F i j k : ℝ)

def formulation : MILPFormulation where
  Params   := Params
  Vars     := Vars
  feasible := Feasible
  obj      := obj

end P20.a
