import argparse
import json


def main(data_path: str, output_path: str) -> None:
    with open(data_path) as f:
        data = json.load(f)

    d = data["d"]
    S = data["S"]
    a = [[int(dij <= S) for dij in di] for di in d]

    params = {
        "nI": data["nI"],
        "m": data["m"],
        "M": data["M"],
        "v": data["v"],
        "a": a,
        "p": data["p"],
    }

    with open(output_path, "w") as f:
        json.dump(params, f, indent=4)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("data", help="Path to data.json")
    parser.add_argument("output", help="Path to write parameters.json")
    args = parser.parse_args()
    main(args.data, args.output)
