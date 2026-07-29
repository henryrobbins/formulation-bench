"""
Generate data.json for the Open-Pit Mine Production Scheduling problem (p17).

Produces a small reproducible instance (10 blocks, 4 periods) adapted from
the Ferchtandiker2025 data generator. The output JSON contains block/period
indices, per-block grades, ore/waste tonnages, NPV values, a precedence
matrix, and capacity/grade bound parameters. The output keys are the
parameters declared in problem.json.

Grades are ore fractions in (0, 1]. The upstream generator instead draws them
from [0.5, 3.0], which contradicts the model it accompanies: that model
partitions blocks into I_0 = {g < 1} and I_1 = {g = 1} and gives a domain to
each part, so any block with g > 1 is left with no domain at all and the MILP
is unbounded. The problem description resolves the conflict in favor of a
fraction — "roughly 20% of blocks are completely made up of ore", the
remainder "contain a fraction of ore" — so I_1 is the pure-ore set, and the
grade bounds below are scaled into (0, 1] to match.
"""

import json
import random
from pathlib import Path

import numpy as np

OUTPUT_PATH = Path(__file__).parent / "data.json"

NUM_BLOCKS = 10
NUM_PERIODS = 4
SEED = 42

# Share of blocks that are entirely ore (grade exactly 1), per the description.
PURE_ORE_SHARE = 0.2

# Revenue per tonne of contained ore. Raised from the upstream 50.0 to offset
# the smaller grade range, keeping every block's NPV non-negative as the
# formulations assume.
ORE_PRICE = 250.0
MINING_COST = 10.0


def generate_data(seed: int = SEED) -> dict:
    np.random.seed(seed)
    random.seed(seed)

    blocks = range(NUM_BLOCKS)
    periods = range(NUM_PERIODS)

    # Per-block ore fraction: exactly 1 for the pure-ore blocks (I_1), a
    # partial fraction for the rest (I_0)
    pure_ore = set(random.sample(list(blocks), round(PURE_ORE_SHARE * NUM_BLOCKS)))
    grade = [
        1.0 if i in pure_ore else float(np.round(np.random.uniform(0.2, 0.99), 2))
        for i in blocks
    ]

    # Ore and waste tonnage
    ore_tonnage = [float(np.random.randint(1000, 5000)) for _ in blocks]
    waste_tonnage = [float(np.random.randint(500, 3000)) for _ in blocks]

    # NPV for each block and period (discounted at 8% per period)
    npv = []
    for i in blocks:
        base_value = (
            grade[i] * ore_tonnage[i] * ORE_PRICE
            - (ore_tonnage[i] + waste_tonnage[i]) * MINING_COST
        )
        npv.append(
            [
                float(
                    np.round(
                        base_value / (1.08**t) * float(np.random.uniform(0.85, 1.15)),
                        2,
                    )
                )
                for t in periods
            ]
        )

    # Precedence: precedence[i][j] = 1 means block i must be mined before j
    precedence = [[0] * NUM_BLOCKS for _ in blocks]
    for j in blocks:
        num_predecessors = np.random.randint(0, min(3, j + 1))
        preds = (
            random.sample(range(j), num_predecessors) if num_predecessors > 0 else []
        )
        for i in preds:
            precedence[i][j] = 1

    # Global capacity and grade bounds
    grade_min = float(np.round(np.random.uniform(0.2, 0.35), 2))
    grade_max = float(np.round(np.random.uniform(0.7, 0.85), 2))
    total_ore = sum(ore_tonnage)
    total_material = total_ore + sum(waste_tonnage)

    return {
        "n": NUM_BLOCKS,
        "t": NUM_PERIODS,
        "c": npv,
        "g": grade,
        "O": ore_tonnage,
        "W": waste_tonnage,
        "G_min": grade_min,
        "G_max": grade_max,
        "PC_min": float(np.round(0.7 * total_ore / NUM_PERIODS, 0)),
        "PC_max": float(np.round(1.2 * total_ore / NUM_PERIODS, 0)),
        "MC_min": float(np.round(0.7 * total_material / NUM_PERIODS, 0)),
        "MC_max": float(np.round(1.2 * total_material / NUM_PERIODS, 0)),
        "P": precedence,
    }


def main() -> None:
    data = generate_data(SEED)
    OUTPUT_PATH.write_text(json.dumps(data, indent=2))
    print(f"Data written to {OUTPUT_PATH}")


if __name__ == "__main__":
    main()
