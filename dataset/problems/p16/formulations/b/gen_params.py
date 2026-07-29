import argparse
import json


def main(data_path: str, output_path: str) -> None:
    with open(data_path) as f:
        data = json.load(f)

    nS = data["nS"]
    M = data["M"]
    nP = data["nP"]

    # F[s][h][p] = 1 iff routing junction s to POI p via hub h is viable:
    #   (1) the detour via the hub costs at most Delta extra minutes
    #   (2) the bike leg takes at most T minutes
    #   (3) the hub is at least D kilometers from the POI
    #   (4) driving to the hub saves at least tau kilometers over driving to the POI
    F = [
        [
            [
                int(
                    data["c_sh"][s][h] + data["b_hp"][h][p] - data["c_sp"][s][p]
                    <= data["Delta"]
                    and data["b_hp"][h][p] <= data["T"]
                    and data["d_hp"][h][p] >= data["D"]
                    and data["d_sp"][s][p] - data["d_sh"][s][h] >= data["tau"]
                )
                for p in range(nP)
            ]
            for h in range(M)
        ]
        for s in range(nS)
    ]

    params = {
        "N": data["N"],
        "M": M,
        "nP": nP,
        "nS": nS,
        "v": data["v"],
        "F": F,
        "U": data["U"],
    }

    with open(output_path, "w") as f:
        json.dump(params, f, indent=4)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("data", help="Path to data.json")
    parser.add_argument("output", help="Path to write parameters.json")
    args = parser.parse_args()
    main(args.data, args.output)
