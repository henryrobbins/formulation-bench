"""Schema checks on each problem's ``problem.json``."""

from __future__ import annotations

from formulation_bench.models import DimensionType
from formulation_bench.problem import Problem


def test_name_and_description_are_present(problem: Problem) -> None:
    assert problem.name.strip(), "empty name"
    assert problem.description.strip(), "empty description.md"


def test_parameter_shapes_resolve(problem: Problem) -> None:
    """Every dimension names another declared parameter.

    Problem data is a plain instance, so its dimensions are either a scalar
    parameter or a ragged ``X[Y]`` pair. The expression and cardinality forms
    depend on a formulation's definitions and have no meaning here.
    """
    scalars = {n for n, p in problem.parameters.items() if p.shape.is_scalar}
    arrays = {n for n, p in problem.parameters.items() if not p.shape.is_scalar}

    for name, parameter in problem.parameters.items():
        for dimension in parameter.shape:
            where = f"parameter {name!r}, dimension {str(dimension)!r}"
            if dimension.type is DimensionType.fixed:
                assert dimension.dim_str in scalars, (
                    f"{where}: not a declared scalar parameter"
                )
            elif dimension.type is DimensionType.ragged:
                assert dimension.array in arrays, (
                    f"{where}: {dimension.array!r} is not a declared array parameter"
                )
                assert parameter.shape.resolve(dimension) is not None, (
                    f"{where}: {dimension.indexed_by!r} is not an earlier dimension"
                )
            else:
                raise AssertionError(f"{where}: {dimension.type.value} dimension")


def test_parameters_are_read_by_gen_params(problem: Problem) -> None:
    """Each declared parameter is read by at least one formulation."""
    scripts = "\n".join(
        (f.path / "gen_params.py").read_text() for f in problem.formulations.values()
    )
    unread = [
        name
        for name in problem.parameters
        if f'"{name}"' not in scripts and f"'{name}'" not in scripts
    ]
    assert not unread, f"declared but read by no gen_params.py: {unread}"


def test_metadata_records_source_and_notes(problem: Problem) -> None:
    source = problem.metadata.get("source")
    assert isinstance(source, dict), "metadata.source is missing or not an object"
    assert "dataset" in source, "metadata.source does not name a dataset"
    assert problem.metadata.get("notes"), "metadata.notes is missing or empty"
