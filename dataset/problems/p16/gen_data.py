"""
Generate data.json for the Park and Bike Hub Location (Mobian) problem (p16).

Produces a small, reproducible instance with a fixed random seed suitable for
testing and benchmarking. The output keys are the parameters declared in
problem.json.

Adapted from dataset/sources/Ferchtandiker2025/mobian/data_generator.py,
using small instance sizes instead of the large dataset sizes.
"""

import json
import random
from pathlib import Path

OUTPUT_PATH = Path(__file__).parent / "data.json"

# Small instance size (appropriate for test/benchmark)
NUM_HUBS = 5
NUM_POIS = 4
NUM_JUNCTIONS = 3


def generate_data(seed: int = 42) -> dict:
    random.seed(seed)

    hubs = range(NUM_HUBS)
    pois = range(NUM_POIS)
    junctions = range(NUM_JUNCTIONS)

    # Generate demand
    demand = [[float(random.randint(20, 200)) for _ in pois] for _ in junctions]

    # Generate distances
    distance_sp = [[round(random.uniform(1, 20), 2) for _ in pois] for _ in junctions]
    distance_sh = [[round(random.uniform(1, 15), 2) for _ in hubs] for _ in junctions]
    distance_hp = [[round(random.uniform(1, 10), 2) for _ in pois] for _ in hubs]

    # Generate travel times
    car_time_sp = [[round(random.uniform(5, 30), 1) for _ in pois] for _ in junctions]
    car_time_sh = [[round(random.uniform(3, 20), 1) for _ in hubs] for _ in junctions]
    bike_time_hp = [[round(random.uniform(5, 25), 1) for _ in pois] for _ in hubs]

    # Scalar parameters
    max_bike_time = round(random.uniform(10, 20), 1)
    num_existing_hubs = random.randint(1, max(1, NUM_HUBS // 2))
    max_new_hubs = random.randint(1, max(1, NUM_HUBS - num_existing_hubs))
    min_hub_poi_distance = round(random.uniform(2, 5), 2)
    max_additional_time = round(random.uniform(15, 45), 1)
    min_distance_diff = round(random.uniform(1, 5), 2)

    return {
        "N": num_existing_hubs,
        "M": NUM_HUBS,
        "nP": NUM_POIS,
        "nS": NUM_JUNCTIONS,
        "v": demand,
        "c_sp": car_time_sp,
        "c_sh": car_time_sh,
        "b_hp": bike_time_hp,
        "d_sp": distance_sp,
        "d_hp": distance_hp,
        "d_sh": distance_sh,
        "T": max_bike_time,
        "U": max_new_hubs,
        "D": min_hub_poi_distance,
        "Delta": max_additional_time,
        "tau": min_distance_diff,
    }


def main() -> None:
    data = generate_data(seed=42)
    OUTPUT_PATH.write_text(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
