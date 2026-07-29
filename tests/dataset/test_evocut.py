"""Structural checks on the EvoCut problems (p6-p12).

Every non-base formulation of an EvoCut problem is formulation ``a`` plus one or
more cuts: it must keep ``a``'s parameters, assumptions, objective, and
variables intact, keep ``a``'s constraints as a prefix, and add at least one
constraint of its own.
"""

from __future__ import annotations

from formulation_bench.formulation import Formulation


def test_parameters_assumptions_objective_match_base(
    evocut_variant: Formulation, evocut_base: Formulation
) -> None:
    assert evocut_variant.parameters == evocut_base.parameters
    assert evocut_variant.assumptions == evocut_base.assumptions
    assert evocut_variant.objective == evocut_base.objective


def test_variables_preserve_base(
    evocut_variant: Formulation, evocut_base: Formulation
) -> None:
    """A variant keeps every variable of ``a`` unchanged; extras are allowed."""
    for name, variable in evocut_base.variables.items():
        assert name in evocut_variant.variables, f"variable {name!r} missing"
        assert evocut_variant.variables[name] == variable, (
            f"variable {name!r} differs from a's"
        )


def test_constraints_extend_base(
    evocut_variant: Formulation, evocut_base: Formulation
) -> None:
    """``a``'s constraints appear as a prefix, followed by at least one cut."""
    base = evocut_base.constraints
    variant = evocut_variant.constraints

    assert len(variant) > len(base), "no extra constraints beyond a's"
    for i, (bc, vc) in enumerate(zip(base, variant)):
        assert vc == bc, f"constraint {i} differs from a's"
