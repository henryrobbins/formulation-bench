import argparse
import json


def main(data_path: str, output_path: str) -> None:
    # This formulation's parameters are fixed; the instance data is unused.
    params = {
        "D": 500,
        "J": 750,
        "A": 100000,
        "O": 4,
        "Q": 10,
    }

    with open(output_path, "w") as f:
        json.dump(params, f, indent=4)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("data", help="Path to data.json")
    parser.add_argument("output", help="Path to write parameters.json")
    args = parser.parse_args()
    main(args.data, args.output)
