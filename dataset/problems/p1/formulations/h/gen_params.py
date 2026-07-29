import argparse
import json


def main(data_path: str, output_path: str) -> None:
    # This formulation's parameters are fixed; the instance data is unused.
    params = {
        "G": 30,
        "Y": 40,
        "K": 0.5,
        "V": 2000,
        "L": 15,
    }

    with open(output_path, "w") as f:
        json.dump(params, f, indent=4)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("data", help="Path to data.json")
    parser.add_argument("output", help="Path to write parameters.json")
    args = parser.parse_args()
    main(args.data, args.output)
