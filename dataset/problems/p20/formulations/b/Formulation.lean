import Common
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic

open BigOperators Finset

namespace P20.b

/-- A candidate edge indicator + rank labeling represents a valid simple
supplier-to-beneficiary path on the graph (N, E) with supplier set S and
beneficiary set B. -/
def IsValidPath {nN nS nB : ℕ}
    (S : Fin nS → Fin nN) (B : Fin nB → Fin nN)
    (E : Fin nN → Fin nN → ℤ)
    (pE : Fin nN → Fin nN → ℤ) (pRank : Fin nN → ℕ) : Prop :=
  -- Path-edge indicator is binary
  (∀ i j : Fin nN, pE i j = 0 ∨ pE i j = 1) ∧
  -- Path edges are a subset of the graph's edges
  (∀ i j : Fin nN, pE i j ≤ E i j) ∧
  -- In-degree of each node within the path is at most 1
  (∀ v : Fin nN, ∑ i : Fin nN, pE i v ≤ 1) ∧
  -- Out-degree of each node within the path is at most 1
  (∀ v : Fin nN, ∑ j : Fin nN, pE v j ≤ 1) ∧
  -- Unique source node, and it is a supplier
  (∃ s : Fin nS,
    (∑ j : Fin nN, pE (S s) j) = 1 ∧
    (∑ i : Fin nN, pE i (S s)) = 0 ∧
    (∀ v : Fin nN,
      (∑ j : Fin nN, pE v j) = 1 ∧ (∑ i : Fin nN, pE i v) = 0 → v = S s)) ∧
  -- Unique sink node, and it is a beneficiary
  (∃ b : Fin nB,
    (∑ i : Fin nN, pE i (B b)) = 1 ∧
    (∑ j : Fin nN, pE (B b) j) = 0 ∧
    (∀ v : Fin nN,
      (∑ i : Fin nN, pE i v) = 1 ∧ (∑ j : Fin nN, pE v j) = 0 → v = B b)) ∧
  -- Acyclicity: rank strictly increases along path edges
  (∀ i j : Fin nN, pE i j = 1 → pRank j = pRank i + 1)

/-- A candidate edge indicator represents a single simple directed cycle on
the graph (N, E): the active edges are a subset of the graph's edges, every
node has in-degree and out-degree at most one with the two equal, and the
active edges form one connected directed cycle rather than a union of two or
more node-disjoint cycles. -/
def IsValidCycle {nN : ℕ}
    (E : Fin nN → Fin nN → ℤ)
    (cE : Fin nN → Fin nN → ℤ) : Prop :=
  -- Cycle-edge indicator is binary
  (∀ i j : Fin nN, cE i j = 0 ∨ cE i j = 1) ∧
  -- Cycle edges are a subset of the graph's edges
  (∀ i j : Fin nN, cE i j ≤ E i j) ∧
  -- In-degree of each node within the cycle is at most 1
  (∀ v : Fin nN, ∑ i : Fin nN, cE i v ≤ 1) ∧
  -- Out-degree of each node within the cycle is at most 1
  (∀ v : Fin nN, ∑ j : Fin nN, cE v j ≤ 1) ∧
  -- In-degree equals out-degree (flow conservation) at every node
  (∀ v : Fin nN, ∑ i : Fin nN, cE i v = ∑ j : Fin nN, cE v j) ∧
  -- The active edges form a single simple directed cycle: there is a closed
  -- walk v₀ → v₁ → ⋯ → v_{m-1} → v₀ through m ≥ 1 distinct nodes whose edges
  -- are exactly the active edges of cE.
  (∃ (m : ℕ) (verts : Fin (m + 1) → Fin nN),
    0 < m ∧
    verts 0 = verts (Fin.last m) ∧
    (∀ i j : Fin (m + 1), i < Fin.last m → j < Fin.last m → verts i = verts j → i = j) ∧
    (∀ u w : Fin nN, cE u w = 1 ↔
      ∃ i : Fin m, verts i.castSucc = u ∧ verts i.succ = w))

structure Params where
  nN : ℕ  -- total number of nodes
  nS : ℕ  -- number of supplier nodes
  nT : ℕ  -- number of transshipment nodes
  nB : ℕ  -- number of beneficiary camps
  nP : ℕ  -- number of simple supplier-to-camp paths
  nC : ℕ  -- number of cycles in the supply network
  nK : ℕ  -- number of commodities
  nL : ℕ  -- number of nutrients
  S : Fin nS → Fin nN  -- maps supplier index to node index
  T : Fin nT → Fin nN  -- maps transshipment index to node index
  B : Fin nB → Fin nN  -- maps beneficiary camp index to node index
  E : Fin nN → Fin nN → ℤ  -- adjacency matrix (1 if edge exists, 0 otherwise)
  pE : Fin nP → Fin nN → Fin nN → ℤ  -- 1 if edge (i, j) is in path p, 0 otherwise
  pRank : Fin nP → Fin nN → ℕ  -- rank/position of node v in path p
  pCost : Fin nP → Fin nK → ℝ  -- shipping cost per kg of commodity k along path p
  cE : Fin nC → Fin nN → Fin nN → ℤ  -- 1 if edge (i, j) is in cycle c, 0 otherwise
  cCost : Fin nC → Fin nK → ℝ  -- shipping cost per kg of commodity k along cycle c
  q : Fin nK → ℝ  -- procurement cost per kg of each commodity
  nutval : Fin nK → Fin nL → ℝ  -- nutritional value per kg of each commodity for each nutrient
  nutreq : Fin nL → ℝ  -- per-person nutritional requirement for each nutrient
  dem : Fin nB → ℝ  -- number of beneficiaries at each camp
  e : Fin nB → Fin nP → ℤ  -- indicator: 1 if path p ends at camp j, 0 otherwise
  -- Assumptions
  hE_bin : ∀ i j : Fin nN, E i j = 0 ∨ E i j = 1
  he_bin : ∀ j : Fin nB, ∀ p : Fin nP, e j p = 0 ∨ e j p = 1
  -- The supplier, transshipment, and beneficiary node-class maps partition N
  hSTB_partition : ∀ v : Fin nN,
    (∃ s : Fin nS, S s = v) ∨ (∃ t : Fin nT, T t = v) ∨ (∃ b : Fin nB, B b = v)
  hSTB_disj_ST : ∀ (s : Fin nS) (t : Fin nT), S s ≠ T t
  hSTB_disj_SB : ∀ (s : Fin nS) (b : Fin nB), S s ≠ B b
  hSTB_disj_TB : ∀ (t : Fin nT) (b : Fin nB), T t ≠ B b
  hS_inj : Function.Injective S
  hT_inj : Function.Injective T
  hB_inj : Function.Injective B
  -- Implicit Assumptions
  hnN : NeZero nN
  hnS : NeZero nS
  hnT : NeZero nT
  hnB : NeZero nB
  hnK : NeZero nK
  hnL : NeZero nL
  hpCost_nn : ∀ p : Fin nP, ∀ k : Fin nK, 0 ≤ pCost p k
  hcCost_nn : ∀ c : Fin nC, ∀ k : Fin nK, 0 ≤ cCost c k
  hq_nn : ∀ k : Fin nK, 0 ≤ q k
  hnutval_nn : ∀ k : Fin nK, ∀ l : Fin nL, 0 ≤ nutval k l
  hnutreq_nn : ∀ l : Fin nL, 0 ≤ nutreq l
  hdem_nn : ∀ j : Fin nB, 0 ≤ dem j
  -- Path validity: every indexed path is a valid simple S-to-B path
  hpE_valid : ∀ p : Fin nP, IsValidPath S B E (pE p) (pRank p)
  -- End indicator e agrees with pE: e_{b,p} = pIn_p(B b) - pOut_p(B b)
  hpE_endE : ∀ b : Fin nB, ∀ p : Fin nP,
    (e b p : ℤ) = (∑ i : Fin nN, pE p i (B b)) - (∑ j : Fin nN, pE p (B b) j)
  -- Completeness: every valid simple S-to-B path is indexed by some p
  hpE_complete : ∀ (pE' : Fin nN → Fin nN → ℤ) (pRank' : Fin nN → ℕ),
    IsValidPath S B E pE' pRank' →
    ∃ p : Fin nP, ∀ i j : Fin nN, pE p i j = pE' i j
  -- Injectivity: distinct path indices give distinct edge sets
  hpE_inj : ∀ p₁ p₂ : Fin nP,
    (∀ i j : Fin nN, pE p₁ i j = pE p₂ i j) → p₁ = p₂
  -- Cycle validity: every indexed cycle is a single simple directed cycle
  hcE_valid : ∀ c : Fin nC, IsValidCycle E (cE c)
  -- Completeness: every valid cycle is indexed by some c
  hcE_complete : ∀ (cE' : Fin nN → Fin nN → ℤ),
    IsValidCycle E cE' →
    ∃ c : Fin nC, ∀ i j : Fin nN, cE c i j = cE' i j
  -- Injectivity: distinct cycle indices give distinct edge sets
  hcE_inj : ∀ c₁ c₂ : Fin nC,
    (∀ i j : Fin nN, cE c₁ i j = cE c₂ i j) → c₁ = c₂

structure Vars (p : Params) where
  x : Fin p.nP → Fin p.nK → ℝ  -- amount of commodity k shipped along path p (kg)
  y : Fin p.nC → Fin p.nK → ℝ  -- amount of commodity k shipped along cycle c (kg)
  R : Fin p.nK → ℝ  -- ration size per person of each commodity (kg)

structure Feasible (p : Params) (v : Vars p) : Prop where
  -- Each camp receives at least its ration demand from paths ending there
  hdemand : ∀ j : Fin p.nB, ∀ k : Fin p.nK,
    p.dem j * v.R k ≤ ∑ π : Fin p.nP, (p.e j π : ℝ) * v.x π k
  -- Rations satisfy all nutritional requirements
  hnutrition : ∀ l : Fin p.nL,
    p.nutreq l ≤ ∑ k : Fin p.nK, p.nutval k l * v.R k
  -- [Implicit Constraints]
  hx_nn : ∀ π : Fin p.nP, ∀ k : Fin p.nK, 0 ≤ v.x π k
  hy_nn : ∀ c : Fin p.nC, ∀ k : Fin p.nK, 0 ≤ v.y c k
  hR_nn : ∀ k : Fin p.nK, 0 ≤ v.R k

-- Minimize total shipping (path and cycle) and procurement cost
def obj (p : Params) (v : Vars p) : ℝ :=
  (∑ π : Fin p.nP, ∑ k : Fin p.nK, p.pCost π k * v.x π k)
    + (∑ c : Fin p.nC, ∑ k : Fin p.nK, p.cCost c k * v.y c k)
    + ∑ k : Fin p.nK, p.q k * (∑ π : Fin p.nP, v.x π k)

def formulation : MILPFormulation where
  Params   := Params
  Vars     := Vars
  feasible := Feasible
  obj      := obj

end P20.b
