from pathlib import Path

import pytest

from formulation_bench import Dataset, Problem

DATASET_ROOT = Path(__file__).resolve().parents[1] / "dataset"


# pytest only calls this hook for initial conftest files, and tests/dataset is
# not one of those under a bare `pytest` run -- so the option the dataset tests
# read has to be registered here.
def pytest_addoption(parser: pytest.Parser) -> None:
    parser.addoption(
        "--problems",
        default=None,
        help=(
            "comma-separated problem numbers the dataset tests are restricted to"
            " (e.g. 6,12); default: all"
        ),
    )


@pytest.fixture
def dataset() -> Dataset:
    return Dataset(DATASET_ROOT)


@pytest.fixture
def problem1(dataset: Dataset) -> Problem:
    return dataset.problems[1]
