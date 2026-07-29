"""
Generate data.json for the UN Humanitarian Disaster Response Hub Location problem.

Randomly generates a set of candidate hub locations, fixed hubs, disaster-prone
regions, affected populations, transportation costs, and travel times.

The output keys are the parameters declared in problem.json.
"""

import json
import random
from pathlib import Path

import numpy as np

SEED = 42
OUTPUT_PATH = Path(__file__).parent / "data.json"


def main() -> None:
    random.seed(SEED)
    np.random.seed(SEED)

    # Set sizes
    num_hubs = random.randint(4, 7)
    num_fixed_hubs = random.randint(1, min(3, num_hubs - 1))
    num_regions = random.randint(5, 10)

    fixed_hubs = sorted(random.sample(range(num_hubs), num_fixed_hubs))
    Hf = [int(h in set(fixed_hubs)) for h in range(num_hubs)]

    # Number of people affected in each region
    a = [random.randint(1000, 10000) for _ in range(num_regions)]

    # Cost per person to transport from hub to region
    C = [
        [round(random.uniform(10, 100), 2) for _ in range(num_regions)]
        for _ in range(num_hubs)
    ]

    # Travel time (hours) from hub to region
    t = [[random.randint(24, 96) for _ in range(num_regions)] for _ in range(num_hubs)]

    # Maximum allowed travel time (hours)
    T = 72

    # Maximum number of hubs that can be opened (including fixed hubs)
    n = random.randint(num_fixed_hubs + 1, num_hubs)

    data = {
        "nH": num_hubs,
        "Hf": Hf,
        "nC": num_regions,
        "a": a,
        "C": C,
        "t": t,
        "T": T,
        "n": n,
    }

    OUTPUT_PATH.write_text(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
