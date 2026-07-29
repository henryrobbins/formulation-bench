import argparse
import json

SUPPLIER, TRANSSHIPMENT, BENEFICIARY = 0, 1, 2


def enumerate_paths(
    nN: int, E: list[list[int]], S: list[int], T: list[int], B: list[int]
) -> list[list[int]]:
    """Simple supplier-to-camp paths, as node-index lists.

    Interior nodes are restricted to transshipment nodes, matching the
    formulation's path-validity assumptions.
    """
    camps, transshipment = set(B), set(T)
    paths: list[list[int]] = []

    def extend(path: list[int]) -> None:
        i = path[-1]
        if i in camps:
            paths.append(list(path))
            return
        for j in range(nN):
            if E[i][j] and j not in path and (j in transshipment or j in camps):
                extend(path + [j])

    for s in S:
        extend([s])
    return paths


def enumerate_cycles(E: list[list[int]], T: list[int]) -> list[list[tuple[int, int]]]:
    """Simple directed cycles through transshipment nodes, as edge lists.

    Cycles are canonicalized to begin at their minimum node index, so
    rotations of the same directed cycle are enumerated exactly once. Only
    transshipment nodes may lie on a cycle, matching the formulation's
    cycle-validity assumptions.
    """
    nodes = sorted(T)
    adj = {i: [j for j in nodes if E[i][j] == 1] for i in nodes}
    cycles: list[list[tuple[int, int]]] = []

    for start in nodes:
        path = [start]
        on_path = {start}

        def dfs(v: int, start: int = start) -> None:
            for w in adj[v]:
                if w == start:
                    edges = list(zip(path, path[1:]))
                    edges.append((v, start))
                    cycles.append(edges)
                elif w > start and w not in on_path:
                    path.append(w)
                    on_path.add(w)
                    dfs(w)
                    path.pop()
                    on_path.discard(w)

        dfs(start)

    return cycles


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

    paths = enumerate_paths(nN, E, S, T, B)
    nP = len(paths)
    cycles = enumerate_cycles(E, T)
    nC = len(cycles)

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

    # cE[c][i][j] = 1 if edge (i -> j) is on cycle c.
    cE = [[[0] * nN for _ in range(nN)] for _ in range(nC)]
    for c, cycle_edges in enumerate(cycles):
        for i, j in cycle_edges:
            cE[c][i][j] = 1

    # Shipping cost along a path or cycle is the sum of its edge costs.
    pCost = [
        [sum(tc[i][j][k] for i, j in zip(path, path[1:])) for k in range(nK)]
        for path in paths
    ]
    cCost = [
        [sum(tc[i][j][k] for i, j in cycle_edges) for k in range(nK)]
        for cycle_edges in cycles
    ]

    params = {
        "nN": nN,
        "nS": len(S),
        "nT": len(T),
        "nB": len(B),
        "nP": nP,
        "nC": nC,
        "nK": nK,
        "nL": data["nL"],
        "S": S,
        "T": T,
        "B": B,
        "E": E,
        "pE": pE,
        "pRank": pRank,
        "pCost": pCost,
        "cE": cE,
        "cCost": cCost,
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
