"""End-to-end solve checks for every formulation in the dataset.

For each formulation, ``gen_params.py`` is run and the generated ``solve.py`` is
executed; valid formulations must reproduce the objective recorded in their
problem's ``solution.json``. Artifacts are written under ``tmp_path`` so the
dataset tree is never mutated.

Matching objectives alone does not pin down the recorded solution: a stored
variable assignment can be infeasible while the objective it is labelled with is
still the true optimum (this is how the p12 MTZ positions went unnoticed). So
formulations stated over exactly the recorded variables are also re-solved with
those variables pinned to their recorded values.
"""

from __future__ import annotations

import json
import math
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

from formulation_bench.formulation import Formulation
from formulation_bench.models import Constraint

#: Relative tolerance when comparing solved objectives to recorded ones.
OBJECTIVE_REL_TOL = 1e-6

#: Formulations whose objective is a scaled copy of the problem's, mapped to
#: that scale factor. They are faithful (same optimal solutions) but their
#: optimal value differs from the recorded one, and the dataset has nowhere to
#: record the factor.
OBJECTIVE_SCALE = {f"p{n}.g": 2 for n in range(1, 6)}

#: Absolute slack allowed when pinning a variable to its recorded value. The
#: recorded values are themselves solver output, so exact equality would make
#: continuous variables spuriously infeasible.
PIN_TOL = 1e-6


def _run_solve(
    formulation: Formulation, tmp_path: Path, on_error: str
) -> dict[str, Any]:
    """Run gen_params -> generated solve.py and return the solution JSON.

    An unsolved model fails inside the generated script (it has no solution to
    extract), so ``on_error`` describes what a non-zero exit means to the caller.
    """
    solve_py = tmp_path / "solve.py"
    solve_py.write_text(formulation.gen_solve_py())

    params = tmp_path / "parameters.json"
    formulation.run_gen_params(output_path=params)

    solution = tmp_path / "solution.json"
    result = subprocess.run(
        [sys.executable, str(solve_py), str(params), str(solution)],
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        pytest.fail(f"{on_error}\n{result.stdout[-2000:]}\n{result.stderr[-2000:]}")

    return json.loads(solution.read_text())  # type: ignore[no-any-return]


def _label(formulation: Formulation) -> str:
    return f"{formulation.problem.path.name}.{formulation.path.name}"


def _rank(value: object) -> int:
    """Number of dimensions of a recorded variable value."""
    rank = 0
    while isinstance(value, list) and value:
        rank += 1
        value = value[0]
    return rank


def _pin_code(name: str, value: object) -> str:
    """gurobipy source pinning variable ``name`` to its recorded ``value``."""
    depth = _rank(value)

    literal = f"_pinned_{name} = {json.dumps(value)}"
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


def _pinned(formulation: Formulation, recorded: dict[str, object]) -> Formulation:
    pinned = formulation
    for name in formulation.variables:
        pinned = pinned.with_constraint(
            Constraint(
                description=f"Pin {name} to its recorded value.",
                formulation="",
                explicit=True,
                code={"gurobipy": _pin_code(name, recorded[name])},
            )
        )
    return pinned


def test_solve_matches_recorded_objective(
    formulation: Formulation, tmp_path: Path
) -> None:
    """The formulation solves, and -- when valid -- attains the recorded objective.

    Invalid formulations are unfaithful by construction, so only their generated
    code is required to execute. Formulations in ``OBJECTIVE_SCALE`` are compared
    against the correspondingly scaled objective.
    """
    solution = _run_solve(formulation, tmp_path, on_error="solve.py failed:")

    if not formulation.valid:
        return
    expected = formulation.problem.solution
    assert expected is not None, "valid formulation with no reference solution"

    actual = solution["objective"]
    target = expected.objective * OBJECTIVE_SCALE.get(_label(formulation), 1)
    assert math.isclose(actual, target, rel_tol=OBJECTIVE_REL_TOL), (
        f"got {actual}, expected {target}"
    )


def test_recorded_solution_is_feasible(
    formulation: Formulation, tmp_path: Path
) -> None:
    """The recorded variable values are feasible and attain the recorded objective.

    Only formulations stated over exactly the recorded variables can be checked
    this way. Reformulations that rename or replace variables (p1-p5, p13.b, ...)
    are skipped: a shared name there does not imply a shared meaning.
    """
    if not formulation.valid:
        pytest.skip("invalid formulation")
    recorded = formulation.problem.solution
    assert recorded is not None, "valid formulation with no reference solution"

    if any(v.indices is not None for v in formulation.variables.values()):
        pytest.skip("indexed variables are not recorded in a pinnable form")
    if not set(formulation.variables) <= set(recorded.variables):
        pytest.skip("formulation is stated over different variables")
    if any(
        _rank(recorded.variables[name]) != len(v.shape)
        for name, v in formulation.variables.items()
    ):
        pytest.skip("a recorded variable of the same name has a different shape")

    solution = _run_solve(
        _pinned(formulation, recorded.variables),
        tmp_path,
        on_error="the recorded solution is infeasible for this formulation:",
    )

    actual = solution["objective"]
    target = recorded.objective * OBJECTIVE_SCALE.get(_label(formulation), 1)
    assert math.isclose(actual, target, rel_tol=OBJECTIVE_REL_TOL), (
        f"got {actual}, expected {target}"
    )
