import argparse
import json

SUPPLIER, TRANSSHIPMENT, BENEFICIARY = 0, 1, 2


def main(data_path: str, output_path: str) -> None:
    with open(data_path) as f:
        data = json.load(f)

    nN = data["nN"]
    node_type = data["node_type"]

    S = [i for i in range(nN) if node_type[i] == SUPPLIER]
    T = [i for i in range(nN) if node_type[i] == TRANSSHIPMENT]
    B = [i for i in range(nN) if node_type[i] == BENEFICIARY]

    params = {
        "nN": nN,
        "nS": len(S),
        "nT": len(T),
        "nB": len(B),
        "nK": data["nK"],
        "nL": data["nL"],
        "S": S,
        "T": T,
        "B": B,
        "E": data["E"],
        "dem": data["dem"],
        "pc": data["pc"],
        "tc": data["tc"],
        "nutreq": data["nutreq"],
        "nutval": data["nutval"],
    }

    with open(output_path, "w") as f:
        json.dump(params, f, indent=4)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("data", help="Path to data.json")
    parser.add_argument("output", help="Path to write parameters.json")
    args = parser.parse_args()
    main(args.data, args.output)
