"""Collection and parametrization for the dataset tests.

These tests check the *content* of ``dataset/`` rather than the package code: a
failure means a data defect. They solve every formulation with Gurobi, so they
take minutes and are excluded from the default pytest run by the ``dataset``
marker (see ``make test-dataset``).

Restrict a run to specific problems with ``--problems``::

    pytest tests/dataset -m dataset --problems 6,12
"""

from __future__ import annotations

from pathlib import Path

import pytest

from formulation_bench import Dataset
from formulation_bench.formulation import Formulation

from ._pinning import is_pinnable

DATASET_ROOT = Path(__file__).resolve().parents[2] / "dataset"

#: Problems taken from the EvoCut dataset, whose formulations are all cut
#: variants of formulation ``a``.
EVOCUT_PROBLEMS = range(6, 13)

# A module-level Dataset is needed so formulations can be enumerated at
# collection time for parametrization.
_DATASET = Dataset(DATASET_ROOT)


def _selected_problems(config: pytest.Config) -> set[int] | None:
    raw = config.getoption("--problems")
    if raw is None:
        return None
    return {int(x.strip()) for x in str(raw).split(",")}


def pytest_collection_modifyitems(
    config: pytest.Config, items: list[pytest.Item]
) -> None:
    # The hook is handed every collected item, not just this directory's.
    here = Path(__file__).parent
    for item in items:
        if item.path is not None and here in item.path.parents:
            item.add_marker(pytest.mark.dataset)


def pytest_generate_tests(metafunc: pytest.Metafunc) -> None:
    selected = _selected_problems(metafunc.config)

    if "problem" in metafunc.fixturenames:
        metafunc.parametrize(
            "problem",
            [
                pytest.param(problem, id=f"p{pid}")
                for pid, problem in _DATASET.problems.items()
                if selected is None or pid in selected
            ],
        )

    if "formulation" in metafunc.fixturenames:
        metafunc.parametrize(
            "formulation",
            [
                pytest.param(f, id=f"p{pid}.{fid}")
                for pid, problem in _DATASET.problems.items()
                if selected is None or pid in selected
                for fid, f in problem.formulations.items()
            ],
        )

    if "pinnable_formulation" in metafunc.fixturenames:
        metafunc.parametrize(
            "pinnable_formulation",
            [
                pytest.param(f, id=f"p{pid}.{fid}")
                for pid, problem in _DATASET.problems.items()
                if selected is None or pid in selected
                for fid, f in problem.formulations.items()
                if is_pinnable(f)
            ],
        )

    if "proved_reformulation" in metafunc.fixturenames:
        metafunc.parametrize(
            "proved_reformulation",
            [
                pytest.param(
                    r, id=f"{r.a.problem.path.name}.{r.a.path.name}_{r.b.path.name}"
                )
                for r in _DATASET.reformulations
                if r.is_reformulation
                and (selected is None or int(r.a.problem.path.name[1:]) in selected)
            ],
        )

    if "reformulation" in metafunc.fixturenames:
        metafunc.parametrize(
            "reformulation",
            [
                pytest.param(
                    r, id=f"{r.a.problem.path.name}.{r.a.path.name}_{r.b.path.name}"
                )
                for r in _DATASET.reformulations
                if selected is None or int(r.a.problem.path.name[1:]) in selected
            ],
        )

    if "evocut_variant" in metafunc.fixturenames:
        metafunc.parametrize(
            "evocut_variant",
            [
                pytest.param(f, id=f"p{pid}.{fid}")
                for pid in EVOCUT_PROBLEMS
                if selected is None or pid in selected
                for fid, f in _DATASET.problems[pid].formulations.items()
                if fid != "a"
            ],
        )


@pytest.fixture
def evocut_base(evocut_variant: Formulation) -> Formulation:
    """The ``a`` formulation the parametrized EvoCut variant derives from."""
    return evocut_variant.problem.formulations["a"]
