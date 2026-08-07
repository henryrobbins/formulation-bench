"""Consistency between each pair's parameter map and its formulations' gen_params.

A reformulation pair's ``map.json`` states how each parameter of ``b`` is
computed from the parameters of ``a``, while each formulation's ``gen_params.py``
computes its own parameters from the problem's ``data.json``. The two are
independent descriptions of the same data, so they must agree: mapping ``a``'s
generated parameters must reproduce ``b``'s.

Only pairs that have a ``map.json`` are collected. Restrict a run to specific
problems with ``--problems``::

    pytest tests/dataset -m dataset --problems 1,14
"""

from __future__ import annotations

import json

from formulation_bench.reformulation import Reformulation


def test_map_agrees_with_gen_params(mapped_reformulation: Reformulation) -> None:
    """Mapping ``a``'s generated parameters reproduces ``b``'s."""
    reform = mapped_reformulation

    reform.a.run_gen_params()
    reform.b.run_gen_params()
    reform.run_map()

    mapped = reform.map_path.parent / "parameters.json"
    assert json.loads(mapped.read_text()) == json.loads(
        (reform.b.path / "parameters.json").read_text()
    )
