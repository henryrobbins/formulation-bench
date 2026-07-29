"""Checks on each problem's recorded instance: ``data.json`` and ``solution.json``."""

from __future__ import annotations

from typing import Any

import pytest

from formulation_bench.models import DimensionType, Shape
from formulation_bench.problem import Problem


def _dimension_length(
    shape: Shape, depth: int, data: dict[str, Any], index: tuple[int, ...]
) -> int:
    """The length the ``depth``-th dimension should have at position ``index``.

    A ragged dimension ``X[Y]`` takes its length from ``X`` at whichever index
    position ``Y`` occupies, so the enclosing indices are needed to resolve it.
    """
    dimension = shape[depth]
    if dimension.type is DimensionType.ragged:
        outer = next(
            i for i, d in enumerate(shape) if d.dim_str == dimension.indexed_by
        )
        return int(data[dimension.array][index[outer]])
    return int(data[dimension.dim_str])


def _shape_errors(
    value: object,
    shape: Shape,
    data: dict[str, Any],
    depth: int = 0,
    index: tuple[int, ...] = (),
) -> list[str]:
    """Ways ``value`` fails to be a rectangular nesting matching ``shape``."""
    at = f" at {list(index)}" if index else ""
    if depth == len(shape):
        return [f"expected a scalar{at}, got a list"] if isinstance(value, list) else []
    if not isinstance(value, list):
        return [f"expected a list{at}, got {type(value).__name__}"]

    expected = _dimension_length(shape, depth, data, index)
    errors = []
    if len(value) != expected:
        errors.append(
            f"dimension {depth} ({str(shape[depth])!r}){at}:"
            f" length {len(value)}, expected {expected}"
        )
    for i, item in enumerate(value):
        errors += _shape_errors(item, shape, data, depth + 1, index + (i,))
    return errors


def _leaves(value: object) -> list[Any]:
    if not isinstance(value, list):
        return [value]
    return [leaf for item in value for leaf in _leaves(item)]


def test_keys_match_declared_parameters(problem: Problem) -> None:
    """``data.json`` and ``problem.json`` name exactly the same parameters."""
    assert problem.data is not None, "no data.json"
    declared, recorded = set(problem.parameters), set(problem.data)
    assert not declared - recorded, (
        f"declared but absent from data.json: {sorted(declared - recorded)}"
    )
    assert not recorded - declared, (
        f"in data.json but not declared: {sorted(recorded - declared)}"
    )


def test_values_match_declared_shape(problem: Problem) -> None:
    assert problem.data is not None, "no data.json"
    errors = [
        f"{name}: {error}"
        for name, parameter in problem.parameters.items()
        if name in problem.data
        for error in _shape_errors(problem.data[name], parameter.shape, problem.data)
    ]
    assert not errors, "\n".join(errors)


def test_values_match_declared_type(problem: Problem) -> None:
    """Integer and binary parameters hold integral (respectively 0/1) values."""
    assert problem.data is not None, "no data.json"
    errors = []
    for name, parameter in problem.parameters.items():
        if name not in problem.data:
            continue
        values = _leaves(problem.data[name])
        if parameter.type.value == "integer":
            offenders = [v for v in values if not float(v).is_integer()]
            if offenders:
                errors.append(f"{name}: declared integer, has {offenders[:5]}")
        elif parameter.type.value == "binary":
            offenders = [v for v in values if v not in (0, 1)]
            if offenders:
                errors.append(f"{name}: declared binary, has {offenders[:5]}")
    assert not errors, "\n".join(errors)


def test_solution_objective_is_numeric(problem: Problem) -> None:
    assert problem.solution is not None, "no solution.json"
    objective = problem.solution.objective
    assert isinstance(objective, (int, float)) and not isinstance(objective, bool), (
        f"objective is {type(objective).__name__}"
    )


def test_solution_variables_match_base_formulation(problem: Problem) -> None:
    """The recorded variables are formulation ``a``'s, in the implied encoding.

    A variable declared with ``indices`` is created over an explicit key set, so
    the solver writes it out as a mapping; every other variable is a plain
    nesting whose depth is its declared rank.
    """
    assert problem.solution is not None, "no solution.json"
    base = problem.formulations.get("a")
    if base is None:
        pytest.skip("no formulation a to interpret the solution against")

    recorded, declared = set(problem.solution.variables), set(base.variables)
    assert recorded == declared, (
        f"solution records {sorted(recorded)}, a declares {sorted(declared)}"
    )

    errors = []
    for name, variable in base.variables.items():
        value = problem.solution.variables[name]
        if variable.indices is not None:
            if not isinstance(value, dict):
                errors.append(
                    f"{name}: indexed variable recorded as {type(value).__name__}"
                )
            continue
        if isinstance(value, dict):
            errors.append(f"{name}: recorded as a mapping but declares no indices")
            continue
        rank = 0
        item: object = value
        while isinstance(item, list) and item:
            rank += 1
            item = item[0]
        if rank != len(variable.shape):
            errors.append(f"{name}: shape {variable.shape} but recorded rank {rank}")
    assert not errors, "\n".join(errors)
