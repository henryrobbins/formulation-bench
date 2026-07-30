"""Schema and code-block checks on every ``formulation.json``."""

from __future__ import annotations

import ast
import json
import re
import subprocess
import sys

from formulation_bench.formulation import Formulation
from formulation_bench.models import DimensionType

#: The optimization sense at the head of an objective's LaTeX, e.g. ``\min\;``
#: or ``Maximize \``. Anchored so that a ``\max`` subscript is not mistaken for
#: the sense of the objective.
SENSE = re.compile(r"\s*\\?(min|max)", re.IGNORECASE)

SENSE_TO_GUROBI = {"min": "GRB.MINIMIZE", "max": "GRB.MAXIMIZE"}


def test_shared_parameters_match_problem(formulation: Formulation) -> None:
    """A parameter named after a problem parameter has the same type and shape."""
    mismatched = {
        name: (declared, parameter)
        for name, parameter in formulation.parameters.items()
        if (declared := formulation.problem.parameters.get(name)) is not None
        and (declared.type, str(declared.shape))
        != (parameter.type, str(parameter.shape))
    }
    assert not mismatched, "\n".join(
        f"{name}: problem.json declares {d.type.value} {d.shape},"
        f" formulation.json declares {f.type.value} {f.shape}"
        for name, (d, f) in mismatched.items()
    )


def test_shapes_resolve(formulation: Formulation) -> None:
    """Every dimension of every parameter and variable names something declared."""
    scalars = {n for n, p in formulation.parameters.items() if p.shape.is_scalar}
    arrays = {n for n, p in formulation.parameters.items() if not p.shape.is_scalar}
    definitions = set(formulation.definitions)

    declarations = [
        ("parameter", formulation.parameters),
        ("variable", formulation.variables),
    ]
    for kind, items in declarations:
        for name, item in items.items():
            for dimension in item.shape:
                where = f"{kind} {name!r}, dimension {str(dimension)!r}"
                if dimension.type is DimensionType.fixed:
                    assert dimension.dim_str in scalars | definitions, (
                        f"{where}: not a scalar parameter or definition"
                    )
                elif dimension.type is DimensionType.ragged:
                    assert dimension.array in arrays | definitions, (
                        f"{where}: {dimension.array!r} is not an array parameter"
                    )
                    assert item.shape.resolve(dimension) is not None, (
                        f"{where}: {dimension.indexed_by!r} is not an earlier dimension"
                    )
                elif dimension.type is DimensionType.cardinality:
                    assert dimension.set_name in definitions, (
                        f"{where}: {dimension.set_name!r} is not a definition"
                    )
                    # The index keys of a set-indexed variable cannot be
                    # inferred from its shape, so codegen needs them spelled out.
                    assert kind == "parameter" or item.indices is not None, (
                        f"{where}: a cardinality dimension requires `indices`"
                    )


def test_assumption_code_asserts_on_parameters(formulation: Formulation) -> None:
    """Assumptions constrain parameters, so they compile to Python assertions."""
    errors = []
    for i, assumption in enumerate(formulation.assumptions):
        if set(assumption.code) != {"python"}:
            errors.append(f"assumption[{i}]: code keys {sorted(assumption.code)}")
        elif "assert" not in assumption.code["python"]:
            errors.append(f"assumption[{i}]: no assert statement")
    assert not errors, "\n".join(errors)


def test_constraint_code_is_present(formulation: Formulation) -> None:
    """Constraints act on the model, so they compile to gurobipy."""
    errors = []
    for i, constraint in enumerate(formulation.constraints):
        if set(constraint.code) != {"gurobipy"}:
            errors.append(f"constraint[{i}]: code keys {sorted(constraint.code)}")
        elif not constraint.code["gurobipy"].strip():
            errors.append(f"constraint[{i}]: empty gurobipy code")
    assert not errors, "\n".join(errors)


def test_definition_code_is_present(formulation: Formulation) -> None:
    """Definitions are computed before the variables, so they compile to Python."""
    errors = []
    for name, definition in formulation.definitions.items():
        if set(definition.code) != {"python"}:
            errors.append(f"definition {name!r}: code keys {sorted(definition.code)}")
        elif not definition.code["python"].strip():
            errors.append(f"definition {name!r}: empty python code")
    assert not errors, "\n".join(errors)


def test_objective_code_matches_declared_sense(formulation: Formulation) -> None:
    """The objective sets a sense, and it is the one its LaTeX states."""
    objective = formulation.objective
    assert set(objective.code) == {"gurobipy"}, f"code keys {sorted(objective.code)}"

    code = objective.code["gurobipy"]
    assert "model.setObjective" in code, "objective does not call model.setObjective"

    match = SENSE.match(objective.formulation)
    assert match is not None, f"LaTeX states no sense: {objective.formulation[:60]!r}"
    expected = SENSE_TO_GUROBI[match.group(1).lower()]
    assert expected in code, (
        f"LaTeX states {match.group(1)!r} but code does not set {expected}"
    )


def test_generated_solve_py_is_valid_python(formulation: Formulation) -> None:
    ast.parse(formulation.gen_solve_py())


def test_generated_solve_py_defines_every_name(formulation: Formulation) -> None:
    """No snippet references a name nothing declares.

    Catches parameters used but never declared, definitions referenced before
    they exist, and third-party modules missing from ``imports``.
    """
    script = formulation.path / "solve.py"
    script.write_text(formulation.gen_solve_py())

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "ruff",
            "check",
            "--select",
            "F821",
            "--no-cache",
            "--output-format",
            "concise",
            str(script),
        ],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stdout or result.stderr


def test_generated_solve_py_includes_every_snippet(formulation: Formulation) -> None:
    """Codegen emits every constraint and the objective, dropping nothing."""
    script = formulation.gen_solve_py()
    blocks = [
        (f"constraint[{i}]", c.code.get("gurobipy", ""))
        for i, c in enumerate(formulation.constraints)
    ] + [("objective", formulation.objective.code.get("gurobipy", ""))]

    missing = [
        f"{label}: {line.strip()[:60]!r}"
        for label, code in blocks
        for line in code.strip().splitlines()
        if line.strip() and line not in script
    ]
    assert not missing, "not emitted into solve.py:\n" + "\n".join(missing)


def test_gen_params_emits_declared_parameters(formulation: Formulation) -> None:
    """``gen_params.py`` writes exactly the parameters the formulation declares.

    The generated ``solve.py`` reads each declared parameter out of this file by
    name, so a missing key fails the solve and an extra one is dead data.
    """
    formulation.run_gen_params()
    output = formulation.path / "parameters.json"
    generated = json.loads(output.read_text())

    declared, emitted = set(formulation.parameters), set(generated)
    assert not declared - emitted, (
        f"declared but not emitted: {sorted(declared - emitted)}"
    )
    assert not emitted - declared, (
        f"emitted but not declared: {sorted(emitted - declared)}"
    )


def test_metadata_records_source(formulation: Formulation) -> None:
    source = formulation.metadata.get("source")
    assert isinstance(source, dict), "metadata.source is missing or not an object"
    assert "dataset" in source, "metadata.source does not name a dataset"
    if "instance_id" in source:
        assert isinstance(source["instance_id"], str), (
            f"instance_id is {type(source['instance_id']).__name__}, expected str"
        )
