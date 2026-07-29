import argparse
import json


def main(data_path: str, output_path: str) -> None:
    with open(data_path) as f:
        data = json.load(f)

    params = {
        "n": data["n"],
        "t": data["t"],
        "c": data["c"],
        "g": data["g"],
        "O": data["O"],
        "W": data["W"],
        "G_min": data["G_min"],
        "G_max": data["G_max"],
        "PC_min": data["PC_min"],
        "PC_max": data["PC_max"],
        "MC_min": data["MC_min"],
        "MC_max": data["MC_max"],
        "P": data["P"],
    }

    with open(output_path, "w") as f:
        json.dump(params, f, indent=4)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("data", help="Path to data.json")
    parser.add_argument("output", help="Path to write parameters.json")
    args = parser.parse_args()
    main(args.data, args.output)
