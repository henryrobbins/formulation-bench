import argparse
import json


def main(data_path: str, output_path: str) -> None:
    with open(data_path) as f:
        data = json.load(f)

    nJ = data["nJ"]
    nV = data["nV"]
    R = data["R"]

    # cap[v]: apartments in configuration v, summed over the floor areas.
    cap = [sum(R[j][v] for j in range(nJ)) for v in range(nV)]
    nA = max(cap)

    # jApt[v][a]: floor-area index of apartment a in configuration v. Apartments
    # within a configuration are interchangeable, so listing each area index
    # R[j][v] times fixes an arbitrary but valid order. Entries past cap[v] pad
    # the row out to nA and are never accessed.
    jApt = [
        [j for j in range(nJ) for _ in range(R[j][v])] + [0] * (nA - cap[v])
        for v in range(nV)
    ]

    params = {
        "nK": data["K"],
        "nV": nV,
        "nH": data["nH"],
        "nI": data["nI"],
        "nJ": nJ,
        "nA": nA,
        "cap": cap,
        "jApt": jApt,
        "pProfit": data["O"],
        "area": data["area"],
        "m": data["m"],
        "b": data["a"],
        "s": data["s"],
        "o": data["o"],
        "iFree": data["iFree"],
        "hCorp": data["hCorp"],
    }

    with open(output_path, "w") as f:
        json.dump(params, f, indent=4)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("data", help="Path to data.json")
    parser.add_argument("output", help="Path to write parameters.json")
    args = parser.parse_args()
    main(args.data, args.output)
