"""Structural checks on the Lean formulations and reformulation proofs."""

from __future__ import annotations

import re

import pytest

from formulation_bench.formulation import Formulation
from formulation_bench.models import VariableType
from formulation_bench.reformulation import Reformulation

#: The Lean carrier for each declared variable domain. Integer and binary
#: variables are both ``ℤ``; a binary is an integer the formulation pins to
#: ``{0, 1}`` with a constraint.
LEAN_CARRIER = {
    VariableType.continuous: "ℝ",
    VariableType.integer: "ℤ",
    VariableType.binary: "ℤ",
}

#: Declarations every ``Formulation.lean`` builds its ``MILPFormulation`` from.
#: ``noncomputable`` prefixes some of them, so these match anywhere on a line.
REQUIRED_DECLARATIONS = (
    "structure Params",
    "structure Vars",
    "structure Feasible",
    "def obj",
    "def formulation : MILPFormulation",
)

_BLOCK_COMMENT = re.compile(r"/-.*?-/", re.DOTALL)
_LINE_COMMENT = re.compile(r"--.*")
_UNFINISHED = re.compile(r"\bsorry\b|\badmit\b|^\s*axiom\b", re.MULTILINE)


def _strip_comments(source: str) -> str:
    return _LINE_COMMENT.sub("", _BLOCK_COMMENT.sub("", source))


def _structure_fields(source: str, structure: str) -> dict[str, str]:
    """Map each field of ``structure`` to the type its declaration ends in."""
    lines = source.splitlines()
    start = next(
        (
            i
            for i, line in enumerate(lines)
            if line.startswith(f"structure {structure}")
        ),
        None,
    )
    if start is None:
        return {}

    signatures: dict[str, str] = {}
    field = None
    indent = None
    for line in lines[start + 1 :]:
        if not line.strip() or not line[0].isspace():
            break
        declaration = _LINE_COMMENT.sub("", line).rstrip()
        if not declaration.strip():
            continue

        current = len(declaration) - len(declaration.lstrip())
        if indent is None:
            indent = current
        if current > indent and field is not None:
            signatures[field] += " " + declaration.strip()
            continue
        if ":" not in declaration:
            continue
        name, _, signature = declaration.partition(":")
        field = name.strip()
        signatures[field] = signature.strip()

    return {
        name: signature.rsplit("→", 1)[-1].strip()
        for name, signature in signatures.items()
    }


def test_formulation_declares_a_milp_formulation(formulation: Formulation) -> None:
    """The Lean file exists, is namespaced after its path, and is complete."""
    path = formulation.lean_formulation_path
    assert path.exists(), "no Formulation.lean"

    source = path.read_text()
    problem_id = formulation.problem.path.name[1:]
    namespace = f"namespace P{problem_id}.{formulation.path.name}"
    assert namespace in source, f"does not declare {namespace!r}"

    missing = [d for d in REQUIRED_DECLARATIONS if d not in source]
    assert not missing, f"missing declarations: {missing}"


def test_formulation_variable_domains_match_declaration(
    formulation: Formulation,
) -> None:
    """Each Lean ``Vars`` field ranges over the domain its JSON type implies.

    Only fields named the same in both files are compared. Several formulations
    rename on the way into Lean (``delta`` to ``δ``, ``C_max`` to ``Cmax``),
    and nothing in the dataset records the correspondence.
    """
    fields = _structure_fields(formulation.lean_formulation_path.read_text(), "Vars")

    mismatched = [
        f"{name}: declared {variable.type.value},"
        f" expected {LEAN_CARRIER[variable.type]}, Lean has {fields[name]}"
        for name, variable in formulation.variables.items()
        if name in fields and fields[name] != LEAN_CARRIER[variable.type]
    ]
    assert not mismatched, "\n".join(mismatched)


def test_formulation_has_no_unfinished_proofs(formulation: Formulation) -> None:
    source = _strip_comments(formulation.lean_formulation_path.read_text())
    assert not _UNFINISHED.search(source), "contains sorry, admit, or an axiom"


def test_proof_constructs_the_labelled_reformulation(
    proved_reformulation: Reformulation,
) -> None:
    """The proof builds a ``MILPReformulation`` for exactly the labelled pair.

    The instance names both formulations in order, so this pins the direction
    too: a proof that ``a`` reformulates ``b`` does not establish the pair as
    the manifest labels it.
    """
    path = proved_reformulation.lean_proof_path
    assert path is not None
    if not path.exists():
        pytest.skip("labelled a reformulation but has no proof file")

    namespace = f"P{proved_reformulation.a.problem.path.name[1:]}"
    instance = (
        f"MILPReformulation {namespace}.{proved_reformulation.a.path.name}.formulation"
        f" {namespace}.{proved_reformulation.b.path.name}.formulation"
    )
    assert instance in path.read_text(), f"does not construct {instance!r}"


def test_proof_has_no_unfinished_proofs(
    proved_reformulation: Reformulation,
) -> None:
    path = proved_reformulation.lean_proof_path
    assert path is not None
    if not path.exists():
        pytest.skip("labelled a reformulation but has no proof file")

    assert not _UNFINISHED.search(_strip_comments(path.read_text())), (
        "contains sorry, admit, or an axiom"
    )
