"""
Generate data.json for the World Food Program Food Distribution problem (p20).

Produces a small, reproducible instance (1 supplier, 2 transshipment nodes,
2 beneficiary camps, 3 food commodities, 3 nutrients) adapted from the
Ferchtandiker2025 data generator, which has no analogue of the transshipment
capacities. The output keys are the parameters declared in problem.json.
"""

import json
import random
from pathlib import Path

SCRIPT_DIR = Path(__file__).parent
OUTPUT_PATH = SCRIPT_DIR / "data.json"

SEED = 42


def generate_data(seed: int = SEED) -> dict:
    random.seed(seed)

    # ------------------------------------------------------------------
    # Sets (small instance)
    # ------------------------------------------------------------------
    nutrients = ["calories", "protein", "iron"]
    foods = ["food_001", "food_002", "food_003"]

    supplier_nodes = ["S1"]
    transshipment_nodes = ["T1", "T2"]
    beneficiary_nodes = ["B1", "B2"]
    nodes = supplier_nodes + transshipment_nodes + beneficiary_nodes

    # ------------------------------------------------------------------
    # Edges
    # ------------------------------------------------------------------
    # Start with no edges, then add deterministically with the seeded RNG.
    edges = {i: {j: 0 for j in nodes} for i in nodes}

    edge_configs = [
        (supplier_nodes, transshipment_nodes, 1.0, 0.0),  # S->T: keep all
        (transshipment_nodes, transshipment_nodes, 1.0, 0.3),  # T->T: remove 30 %
        (transshipment_nodes, beneficiary_nodes, 1.0, 0.0),  # T->B: keep all
        (supplier_nodes, beneficiary_nodes, 1.0, 0.5),  # S->B: remove 50 %
    ]

    for source_list, target_list, _create, remove_prob in edge_configs:
        for src in source_list:
            for tgt in target_list:
                if src != tgt:
                    edges[src][tgt] = 1
                    if random.random() < remove_prob:
                        edges[src][tgt] = 0

    # ------------------------------------------------------------------
    # Parameters
    # ------------------------------------------------------------------
    # Camps hold a few hundred people, well below the 15k-50k of the source
    # generator, so that shipping whole kilograms is a meaningful restriction
    # rather than a rounding artifact on tens of tonnes.
    demand = {b: random.randint(150, 500) for b in beneficiary_nodes}

    nutritional_requirements = {
        "calories": 2500,
        "protein": 56,
        "iron": 14,
    }

    # Nutritional values per kg of each food (per nutrient)
    food_profiles = {
        "food_001": {"calories": 3400, "protein": 80, "iron": 5.0},  # grain
        "food_002": {"calories": 3200, "protein": 150, "iron": 12.0},  # legume
        "food_003": {"calories": 4000, "protein": 70, "iron": 8.0},  # dairy
    }
    nutritional_values = {
        k: {
            l: round(food_profiles[k][l] * random.uniform(0.95, 1.05), 4)
            for l in nutrients
        }
        for k in foods
    }

    # Procurement cost per kg
    procurement_costs = {
        "food_001": round(0.7 + random.uniform(0.0, 0.2), 2),
        "food_002": round(1.1 + random.uniform(0.0, 0.2), 2),
        "food_003": round(1.3 + random.uniform(0.0, 0.2), 2),
    }

    # Edge costs per kg: (node_i, node_j, food_k) -> cost
    # 999999.99 for non-existent edges (mirrors source convention)
    edge_costs = {i: {j: {k: 999999.99 for k in foods} for j in nodes} for i in nodes}
    for i in nodes:
        for j in nodes:
            if i == j or edges[i][j] == 0:
                continue
            for k in foods:
                if i in supplier_nodes and j in transshipment_nodes:
                    base = 0.8
                elif i in transshipment_nodes and j in beneficiary_nodes:
                    base = 1.2
                elif i in transshipment_nodes and j in transshipment_nodes:
                    base = 0.5
                else:
                    base = 1.5
                edge_costs[i][j][k] = round(base + random.uniform(0.2, 0.5), 2)

    # Throughput capacity per transshipment point. Sized off a nominal ration
    # so the hubs can jointly serve every beneficiary but none can do so alone,
    # which forces the flow to split across hubs. Drawn last to keep the values
    # above independent of this block.
    NOMINAL_RATION = 1.5
    total_beneficiaries = sum(demand.values())
    capacities = {
        t: round(
            total_beneficiaries
            * NOMINAL_RATION
            / len(transshipment_nodes)
            * random.uniform(0.95, 1.05)
        )
        for t in transshipment_nodes
    }

    # ------------------------------------------------------------------
    # Assemble
    # ------------------------------------------------------------------
    SUPPLIER, TRANSSHIPMENT, BENEFICIARY = 0, 1, 2
    node_type = (
        [SUPPLIER] * len(supplier_nodes)
        + [TRANSSHIPMENT] * len(transshipment_nodes)
        + [BENEFICIARY] * len(beneficiary_nodes)
    )

    return {
        "nN": len(nodes),
        "nT": len(transshipment_nodes),
        "nB": len(beneficiary_nodes),
        "nK": len(foods),
        "nL": len(nutrients),
        "node_type": node_type,
        "E": [[edges[i][j] for j in nodes] for i in nodes],
        "dem": [demand[b] for b in beneficiary_nodes],
        "cap": [capacities[t] for t in transshipment_nodes],
        "pc": [procurement_costs[k] for k in foods],
        "tc": [[[edge_costs[i][j][k] for k in foods] for j in nodes] for i in nodes],
        "nutreq": [nutritional_requirements[l] for l in nutrients],
        "nutval": [[nutritional_values[k][l] for l in nutrients] for k in foods],
    }


def main() -> None:
    data = generate_data(seed=SEED)
    OUTPUT_PATH.write_text(json.dumps(data, indent=2))
    print(f"Data written to {OUTPUT_PATH}")


if __name__ == "__main__":
    main()
