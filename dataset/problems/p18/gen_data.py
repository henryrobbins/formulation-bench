"""
Generate data.json for the Timor-Leste Hospital Location problem (p18).

Produces a small reproducible instance (~10 households, 3 existing hospitals,
5 candidate sites) adapted from the source data generator in
dataset/sources/Ferchtandiker2025/timor_leste/data_generator.py.

The output keys are the parameters declared in problem.json.
"""

import json
import math
import random
from pathlib import Path

OUTPUT_PATH = Path(__file__).parent / "data.json"

# Instance size parameters
N = 10  # Number of households
M_EX = 3  # Number of existing hospitals
NUM_NEW = 5  # Number of candidate hospital sites
S = 40.0  # Max allowed travel distance (km, generous for small grid)
P = 3  # Max new hospitals to open


def _rand_coords(rng: random.Random, n: int) -> list[tuple[float, float]]:
    """Return n random (x, y) points uniformly in [0, 100]^2."""
    return [(rng.uniform(0, 100), rng.uniform(0, 100)) for _ in range(n)]


def _euclidean(p: tuple[float, float], q: tuple[float, float]) -> float:
    return math.sqrt((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2)


def generate_data(seed: int = 42) -> dict:
    """Generate a small Timor-Leste hospital location instance."""
    rng = random.Random(seed)

    # Hospital sites are indexed with the existing ones first.
    M = M_EX + NUM_NEW

    # Random coordinates on a 100x100 grid
    household_coords = _rand_coords(rng, N)
    hospital_coords = _rand_coords(rng, M)

    population = [rng.randint(50, 499) for _ in range(N)]

    # Travel distances (Euclidean with small noise, rounded)
    travel_distances = [
        [
            round(
                _euclidean(household_coords[i], hospital_coords[j])
                + rng.uniform(-5, 5),
                2,
            )
            for j in range(M)
        ]
        for i in range(N)
    ]

    return {
        "nI": N,
        "m": M_EX,
        "M": M,
        "v": population,
        "d": travel_distances,
        "S": S,
        "p": P,
    }


def main() -> None:
    data = generate_data(seed=42)
    OUTPUT_PATH.write_text(json.dumps(data, indent=2))
    print(f"Data written to {OUTPUT_PATH}")


if __name__ == "__main__":
    main()
