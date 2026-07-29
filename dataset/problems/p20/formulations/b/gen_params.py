import argparse
import json

SUPPLIER, TRANSSHIPMENT, BENEFICIARY = 0, 1, 2


def enumerate_paths(nN: int, E: list[list[int]], S: list[int], B: list[int]):
    """Simple paths from a supplier to a beneficiary camp, as node-index lists."""
    camps = set(B)
    paths: list[list[int]] = []

    def extend(path: list[int]) -> None:
        i = path[-1]
        if i in camps:
            paths.append(list(path))
            return
        for j in range(nN):
            if E[i][j] and j not in path:
                extend(path + [j])

    for s in S:
        extend([s])
    return paths


def main(data_path: str, output_path: str) -> None:
    with open(data_path) as f:
        data = json.load(f)

    nN = data["nN"]
    nK = data["nK"]
    node_type = data["node_type"]
    E = data["E"]
    tc = data["tc"]

    S = [i for i in range(nN) if node_type[i] == SUPPLIER]
    T = [i for i in range(nN) if node_type[i] == TRANSSHIPMENT]
    B = [i for i in range(nN) if node_type[i] == BENEFICIARY]

    paths = enumerate_paths(nN, E, S, B)
    nP = len(paths)

    # pE[p][i][j] = 1 if edge (i -> j) is on path p.
    # pRank[p][v] = position of v along path p; 0 for nodes off the path, which
    # is unconstrained since pRank is only compared where pE[p][i][j] = 1.
    pE = [[[0] * nN for _ in range(nN)] for _ in range(nP)]
    pRank = [[0] * nN for _ in range(nP)]
    for p, path in enumerate(paths):
        for pos, v in enumerate(path):
            pRank[p][v] = pos
        for i, j in zip(path, path[1:]):
            pE[p][i][j] = 1

    # Shipping cost along a path is the sum of its edge costs.
    c = [
        [sum(tc[i][j][k] for i, j in zip(path, path[1:])) for k in range(nK)]
        for path in paths
    ]

    params = {
        "nN": nN,
        "nS": len(S),
        "nT": len(T),
        "nB": len(B),
        "nP": nP,
        "nK": nK,
        "nL": data["nL"],
        "S": S,
        "T": T,
        "B": B,
        "E": E,
        "pE": pE,
        "pRank": pRank,
        "c": c,
        "q": data["pc"],
        "nutval": data["nutval"],
        "nutreq": data["nutreq"],
        "dem": data["dem"],
        "e": [[int(path[-1] == j) for path in paths] for j in B],
    }

    with open(output_path, "w") as f:
        json.dump(params, f, indent=4)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("data", help="Path to data.json")
    parser.add_argument("output", help="Path to write parameters.json")
    args = parser.parse_args()
    main(args.data, args.output)
