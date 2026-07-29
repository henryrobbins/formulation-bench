"""End-to-end solve checks for every formulation in the dataset.

For each formulation, ``gen_params.py`` is run and the generated ``solve.py`` is
executed; valid formulations must reproduce the objective recorded in their
problem's ``solution.json``. Artifacts are written under ``tmp_path`` so the
dataset tree is never mutated.

Matching objectives alone does not pin down the recorded solution: a stored
variable assignment can be infeasible while the objective it is labelled with is
still the true optimum (this is how the p12 MTZ positions went unnoticed). So
formulations stated over exactly the recorded variables are also re-solved with
those variables pinned to their recorded values (see ``_pinning``).
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

from ._pinning import pinned

#: Relative tolerance when comparing solved objectives to recorded ones.
OBJECTIVE_REL_TOL = 1e-6

#: Formulations whose objective is a scaled copy of the problem's, mapped to
#: that scale factor. They are faithful (same optimal solutions) but their
#: optimal value differs from the recorded one, and the dataset has nowhere to
#: record the factor.
OBJECTIVE_SCALE = {f"p{n}.g": 2 for n in range(1, 6)}

#: Gurobi's error when a model exceeds the 2000 rows/columns of the
#: size-limited license bundled with gurobipy on PyPI.
SIZE_LIMIT_ERROR = "Model too large for size-limited license"


def _run_solve(
    formulation: Formulation, tmp_path: Path, on_error: str
) -> dict[str, Any]:
    """Run gen_params -> generated solve.py and return the solution JSON.

    An unsolved model fails inside the generated script (it has no solution to
    extract), so ``on_error`` describes what a non-zero exit means to the caller.
    Models the available license is too small for are skipped rather than failed.
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
        if SIZE_LIMIT_ERROR in result.stdout + result.stderr:
            pytest.skip("model exceeds the size-limited license")
        pytest.fail(f"{on_error}\n{result.stdout[-2000:]}\n{result.stderr[-2000:]}")

    return json.loads(solution.read_text())  # type: ignore[no-any-return]


def _label(formulation: Formulation) -> str:
    return f"{formulation.problem.path.name}.{formulation.path.name}"


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
    pinnable_formulation: Formulation, tmp_path: Path
) -> None:
    """The recorded variable values are feasible and attain the recorded objective.

    Parametrized over the formulations stated in terms of the recorded variables;
    the rest cannot be checked this way and are not collected.
    """
    formulation = pinnable_formulation
    recorded = formulation.problem.solution
    assert recorded is not None, "pinnable formulation with no reference solution"

    solution = _run_solve(
        pinned(formulation, recorded.variables),
        tmp_path,
        on_error="the recorded solution is infeasible for this formulation:",
    )

    actual = solution["objective"]
    target = recorded.objective * OBJECTIVE_SCALE.get(_label(formulation), 1)
    assert math.isclose(actual, target, rel_tol=OBJECTIVE_REL_TOL), (
        f"got {actual}, expected {target}"
    )
