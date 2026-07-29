"""
Generate data.json for the Dutch Housing Problem (p15).

Adapted from dataset/sources/Ferchtandiker2025/dutch_housing_problem/data_generator.py.
Uses a small instance (10 floors) with a fixed seed (42) for reproducibility.

The output keys are the parameters declared in problem.json.
"""

import json
import random
from pathlib import Path

import numpy as np

OUTPUT_PATH = Path(__file__).parent / "data.json"

TOTAL_FLOORS = 5
SEED = 42


def generate_data(seed: int = SEED, total_floors: int = TOTAL_FLOORS) -> dict:
    random.seed(seed)
    np.random.seed(seed)

    # Sets
    sectors = ["social", "middle", "free"]  # I
    areas = [36, 42, 48, 52, 58, 60, 71]  # J
    # NOTE: We're using a smaller instance than considered in the original paper
    # areas = [36, 42, 48, 52, 58, 60, 68, 70, 71, 96, 131]  # J
    owners = ["corporation", "investor", "private"]  # H

    # Floor parts and their apartment areas
    floor_parts = {
        "a": [36, 36, 42, 42, 48, 48],
        "b": [42, 42, 52, 52, 58],
        "c": [60, 60, 71, 71],
        # NOTE: We're using a smaller instance than considered in the original paper
        # "d": [70, 96, 96],
        # "e": [131, 131],
    }

    # Generate all possible floor configurations (V) as all 2-part combinations
    # (with replacement), e.g. "aa", "ab", ..., "ee"
    part_keys = list(floor_parts.keys())
    floor_configurations = []
    for i in range(len(part_keys)):
        for j in range(i, len(part_keys)):
            floor_configurations.append(part_keys[i] + part_keys[j])

    # The apartment areas each configuration is built from
    config_areas = [floor_parts[v[0]] + floor_parts[v[1]] for v in floor_configurations]

    # R_{jv}: count of apartments of area j in configuration v
    R = [[apt_areas.count(j) for apt_areas in config_areas] for j in areas]

    # Profit per apartment (O_{ijh}): the social sector earns least, the free
    # sector most, scaled by floor area and discounted for non-investor owners.
    O = []
    for i in sectors:
        base = 10000 if i == "social" else (20000 if i == "middle" else 30000)
        rows = []
        for j in areas:
            area_factor = (j - min(areas)) / (max(areas) - min(areas))
            rows.append(
                [
                    int(
                        base
                        * (1 + 0.5 * area_factor)
                        * (1.0 if h == "investor" else (0.9 if h == "private" else 0.8))
                        + random.randint(-1000, 1000)
                    )
                    for h in owners
                ]
            )
        O.append(rows)

    # Minimal area per sector/owner (m_{ih}); 36 is the smallest area available
    min_area = {("social", "corporation"): 40, ("middle", "corporation"): 50}
    m = [
        [60 if i == "free" else min_area.get((i, h), 36) for h in owners]
        for i in sectors
    ]

    # Minimum share of apartments per sector and per owner class, and minimum
    # average area per sector
    min_sector_share = {"social": 0.4, "middle": 0.4, "free": 0.0}
    min_avg_area = {"social": 40, "middle": 50, "free": 60}
    min_owner_share = {"corporation": 0.0, "investor": 0.7, "private": 0.0}

    return {
        "nI": len(sectors),
        "nJ": len(areas),
        "nH": len(owners),
        "nV": len(floor_configurations),
        "K": total_floors,
        "R": R,
        "O": O,
        "area": areas,
        "m": m,
        "a": [min_sector_share[i] for i in sectors],
        "s": [min_avg_area[i] for i in sectors],
        "o": [min_owner_share[h] for h in owners],
        "iFree": sectors.index("free"),
        "hCorp": owners.index("corporation"),
    }


def main() -> None:
    data = generate_data()
    OUTPUT_PATH.write_text(json.dumps(data, indent=2))
    print(f"Data written to {OUTPUT_PATH}")


if __name__ == "__main__":
    main()
