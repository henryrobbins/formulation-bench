"""
Generate data.json for the Air Traffic Flow Management problem (p13).

Generates a synthetic instance with a fleet split into plane classes, a set of
locations (airports/sectors), and a discrete time horizon. Adjacency between
locations is drawn at random (with self-adjacency forced to 1) and each class
draws its own rewards uniformly at random.

Each class is routed along a random walk, which guarantees that the instance
is feasible. Capacities are the location counts induced by those walks plus a
small random slack, so they are tight enough to make the classes compete for
capacity. The chosen seed yields an instance whose LP relaxation is fractional.

Output keys match problem.json:
  nK   -- number of plane classes
  nP   -- list (nK) of the number of flights in each class
  nA   -- number of locations (airports/sectors)
  nT   -- number of time periods
  adj  -- 2-D list (nA x nA) of binary adjacency entries
  r    -- 3-D list (nK x nA x nT) of rewards for a class k flight at (a, t)
  cap  -- 2-D list (nA x nT) of integer capacity of location a at time t
"""

import json
import random
from pathlib import Path

import numpy as np

SCRIPT_DIR = Path(__file__).parent
OUTPUT_PATH = SCRIPT_DIR / "data.json"

SEED = 54
CLASS_SIZES = [2, 2, 1]  # nP
NUM_LOCATIONS = 5  # nA
NUM_TIME_PERIODS = 8  # nT
CAP_SLACK = 2


def generate_data(
    seed: int = SEED,
    class_sizes: list[int] = CLASS_SIZES,
    num_locations: int = NUM_LOCATIONS,
    num_time_periods: int = NUM_TIME_PERIODS,
    cap_slack: int = CAP_SLACK,
) -> dict:
    np.random.seed(seed)
    random.seed(seed)

    nK = len(class_sizes)
    nP = list(class_sizes)
    nA = num_locations
    nT = num_time_periods

    # Adjacency: 1 on diagonal (self-adjacency), random 0/1 off-diagonal
    adj = [
        [1 if a == a2 else int(np.random.randint(0, 2)) for a2 in range(nA)]
        for a in range(nA)
    ]

    # Rewards: non-negative floats, rounded to 1 decimal place, per class
    r = [
        [
            [round(float(np.random.uniform(0.0, 10.0)), 1) for t in range(nT)]
            for a in range(nA)
        ]
        for k in range(nK)
    ]

    # Reference routing: one random walk per class
    walks = []
    for k in range(nK):
        walk = [random.randrange(nA)]
        for _ in range(nT - 1):
            neighbors = [a2 for a2 in range(nA) if adj[walk[-1]][a2] == 1]
            walk.append(random.choice(neighbors))
        walks.append(walk)

    # Capacities: the reference routing's location counts plus a small slack
    cap = [[0] * nT for _ in range(nA)]
    for k in range(nK):
        for t, a in enumerate(walks[k]):
            cap[a][t] += nP[k]
    cap = [
        [cap[a][t] + int(np.random.randint(0, cap_slack + 1)) for t in range(nT)]
        for a in range(nA)
    ]

    return {
        "nK": nK,
        "nP": nP,
        "nA": nA,
        "nT": nT,
        "adj": adj,
        "r": r,
        "cap": cap,
    }


def main() -> None:
    data = generate_data()
    OUTPUT_PATH.write_text(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
