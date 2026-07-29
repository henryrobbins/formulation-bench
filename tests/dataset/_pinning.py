"""Pinning a problem's recorded solution into one of its formulations.

``solution.json`` records variable values under formulation ``a``'s names, so
only formulations stated over those same variables can be pinned. :func:`is_pinnable`
decides that, and is used at collection time so unpinnable formulations are never
parametrized rather than skipped one by one.
"""

from __future__ import annotations

import json

from formulation_bench.formulation import Formulation
from formulation_bench.models import Constraint

#: Absolute slack allowed when pinning a variable to its recorded value. The
#: recorded values are themselves solver output, so exact equality would make
#: continuous variables spuriously infeasible.
PIN_TOL = 1e-6


def _rank(value: object) -> int:
    """Number of dimensions of a recorded variable value."""
    rank = 0
    while isinstance(value, list) and value:
        rank += 1
        value = value[0]
    return rank


def _index_keys(value: object) -> list[list[int]] | None:
    """The index tuples of a recorded indexed variable, or None if not one.

    Indexed variables are recorded as a mapping from a JSON-encoded index tuple
    to a scalar -- the form the generated ``solve.py`` writes them in.
    """
    if not isinstance(value, dict) or not value:
        return None
    keys = []
    for key in value:
        try:
            index = json.loads(key)
        except json.JSONDecodeError:
            return None
        if not isinstance(index, list):
            return None
        keys.append(index)
    return keys


def is_pinnable(formulation: Formulation) -> bool:
    """Whether the problem's recorded solution can be pinned into ``formulation``.

    False for invalid formulations, which are unfaithful by construction, and for
    reformulations that rename or replace variables (p1-p5, p13.b, ...): a shared
    name there does not imply a shared meaning, so a mismatch in kind or shape
    against the recorded value is taken as a different variable.
    """
    if not formulation.valid:
        return False
    recorded = formulation.problem.solution
    if recorded is None or not set(formulation.variables) <= set(recorded.variables):
        return False

    for name, variable in formulation.variables.items():
        value = recorded.variables[name]
        if variable.indices is not None:
            if _index_keys(value) is None:
                return False
        elif _rank(value) != len(variable.shape):
            return False
    return True


def _pin_code(name: str, value: object) -> str:
    """gurobipy source pinning variable ``name`` to its recorded ``value``."""
    literal = f"_pinned_{name} = {json.dumps(value)}"

    if _index_keys(value) is not None:
        pinned = f"_pinned_{name}.items()"
        var = f"{name}[tuple(json.loads(_k))]"
        return "\n".join(
            [
                literal,
                f"model.addConstrs({var} <= _v + {PIN_TOL} for _k, _v in {pinned})",
                f"model.addConstrs({var} >= _v - {PIN_TOL} for _k, _v in {pinned})",
            ]
        )

    depth = _rank(value)
    if depth == 0:
        return "\n".join(
            [
                literal,
                f"model.addConstr({name} <= _pinned_{name} + {PIN_TOL})",
                f"model.addConstr({name} >= _pinned_{name} - {PIN_TOL})",
            ]
        )

    idx = [f"_i{k}" for k in range(depth)]
    recorded = f"_pinned_{name}" + "".join(f"[{i}]" for i in idx)
    loops = " ".join(
        f"for {idx[k]} in range(len(_pinned_{name}"
        + "".join(f"[{i}]" for i in idx[:k])
        + "))"
        for k in range(depth)
    )
    var = f"{name}[{', '.join(idx)}]"
    return "\n".join(
        [
            literal,
            f"model.addConstrs({var} <= {recorded} + {PIN_TOL} {loops})",
            f"model.addConstrs({var} >= {recorded} - {PIN_TOL} {loops})",
        ]
    )


def pinned(formulation: Formulation, recorded: dict[str, object]) -> Formulation:
    """``formulation`` with every variable fixed to its recorded value."""
    result = formulation
    for name in formulation.variables:
        result = result.with_constraint(
            Constraint(
                description=f"Pin {name} to its recorded value.",
                formulation="",
                explicit=True,
                code={"gurobipy": _pin_code(name, recorded[name])},
            )
        )
    return result
