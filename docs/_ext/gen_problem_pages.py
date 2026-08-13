"""Sphinx extension: generate one Markdown page per dataset problem.

Loads the FormulationBench dataset via :mod:`formulation_bench` and writes
``docs/problems/pN.md`` for every problem, plus an ``index.md``
toctree. Pages render each formulation's parameters, variables,
assumptions, constraints, and objective from the LaTeX fields in
``formulation.json``, and render any ``metadata.notes`` (list of markdown
strings) as bullets inside a ``{note}`` admonition. Each page ends with a
Reformulations section listing the problem's labelled pairs and their
parameter maps.

The generated directory is git-ignored; rebuild it with ``sphinx-build``
(this extension runs on the ``builder-inited`` event).
"""
# ruff: noqa: E501

from __future__ import annotations

from collections.abc import Iterable
from pathlib import Path

from formulation_bench import Dataset
from formulation_bench.formulation import Formulation
from formulation_bench.models import (
    Definition,
    Objective,
    Parameter,
    Shape,
    Variable,
)
from formulation_bench.reformulation import Reformulation

SOURCE_LINKS = {
    "EquivaFormulation": (
        "https://huggingface.co/datasets/humainlab/EquivaFormulation"
    ),
    "EvoCut": "https://arxiv.org/abs/2508.11850",
    "Ferchtandiker2025": (
        "https://github.com/nathan-ferchtandiker/LLMs-For-Optimization-Reformulations"
    ),
}

# Every source carries a `citekey` naming an entry in dataset/ref.bib, which
# sphinxcontrib-bibtex resolves against the bibliography on docs/citations.md.


def _fmt_shape(shape: Shape) -> str:
    if shape.is_scalar:
        return "*scalar*"
    return "`[" + ", ".join(d.dim_str for d in shape) + "]`"


def _params_table(params: dict[str, Parameter]) -> str:
    if not params:
        return "_(none)_\n"
    rows = ["| Name | Description | Type | Shape |", "|---|---|---|---|"]
    for name, p in params.items():
        rows.append(
            f"| `{name}` | {p.description} | {p.type.value} | {_fmt_shape(p.shape)} |"
        )
    return "\n".join(rows) + "\n"


def _vars_table(variables: dict[str, Variable]) -> str:
    if not variables:
        return "_(none)_\n"
    rows = ["| Name | Description | Type | Shape / Indices |", "|---|---|---|---|"]
    for name, v in variables.items():
        if v.indices is not None:
            shape_cell = f"`{v.indices}`"
        else:
            shape_cell = _fmt_shape(v.shape)
        rows.append(f"| `{name}` | {v.description} | {v.type.value} | {shape_cell} |")
    return "\n".join(rows) + "\n"


def _math_table(items: Iterable, label: str) -> str:
    items = list(items)
    if not items:
        return f"_(no {label})_\n"
    rows = ["| Description | Formulation | Implicit |", "|---|---|---|"]
    for item in items:
        # Inline math in a table cell needs single $...$; pipes inside the
        # LaTeX must be escaped so they don't break the table column.
        formula = item.formulation.replace("|", r"\|")
        implicit = "no" if item.explicit else "yes"
        rows.append(f"| {item.description} | ${formula}$ | {implicit} |")
    return "\n".join(rows) + "\n"


def _constraints_list(items: Iterable) -> str:
    items = list(items)
    if not items:
        return "_(no constraints)_\n"
    out = []
    for item in items:
        tag = "" if item.explicit else " _(implicit)_"
        out.append(f"- {item.description}{tag}")
        out.append("")
        out.append(f"  $$ {item.formulation} $$")
        out.append("")
    return "\n".join(out)


def _objective_block(obj: Objective) -> str:
    return f"{obj.description}\n\n$$ {obj.formulation} $$\n"


def _formulation_target(pid: int, fid: str) -> str:
    return f"p{pid}-f{fid}"


def _formulation_section(pid: int, fid: str, f: Formulation) -> str:
    badge = "valid" if f.valid else "invalid"
    parts = [
        f"({_formulation_target(pid, fid)})=",
        "",
        f"### Formulation `{fid}` ({badge})\n",
    ]
    src = f.metadata.get("source")
    if src:
        parts += [
            "```{seealso}",
            f"This formulation is sourced from {_source_label(src)}.",
            "```",
            "",
        ]
    note_block = _notes_admonition(f.metadata.get("notes"))
    if note_block:
        parts += [note_block, ""]
    parts += [
        "#### Parameters\n",
        _params_table(f.parameters),
        "",
    ]
    if f.definitions:
        parts.append("#### Definitions\n")
        rows = ["| Name | Description | Formulation |", "|---|---|---|"]
        for name, d in f.definitions.items():
            formula = d.formulation.replace("|", r"\|")
            rows.append(f"| `{name}` | {d.description} | ${formula}$ |")
        parts.append("\n".join(rows) + "\n")
        parts.append("")
    parts += [
        "#### Variables\n",
        _vars_table(f.variables),
        "",
        "#### Assumptions\n",
        _math_table(f.assumptions, "assumptions"),
        "",
        "#### Constraints\n",
        _constraints_list(f.constraints),
        "#### Objective\n",
        _objective_block(f.objective),
    ]
    return "\n".join(parts)


def _source_label(src: object) -> str:
    """Render a ``metadata.source`` as prose.

    A source cites a work by ``citekey``; a source that is one of the
    collected datasets also names it, which takes the lead and links to its
    homepage. Any remaining keys are appended as parenthesized detail. A
    formulation reproduced from one work but first proposed in another
    records the latter under ``origin``.
    """
    if not isinstance(src, dict):
        return str(src)
    cite = src.get("citekey")
    name = src.get("dataset")
    if name:
        url = SOURCE_LINKS.get(name)
        head = f"[{name}]({url})" if url else name
        head += f" {{cite:p}}`{cite}`" if cite else ""
    else:
        head = f"{{cite:t}}`{cite}`" if cite else "?"
    skip = {"dataset", "citekey", "origin"}
    extras = [f"{k.replace('_', ' ')}: {v}" for k, v in src.items() if k not in skip]
    origin = src.get("origin")
    if isinstance(origin, dict) and "citekey" in origin:
        extras.append(f"originally due to {{cite:t}}`{origin['citekey']}`")
    return head + (f" ({', '.join(extras)})" if extras else "")


def _np_hard_label(np_hard: bool) -> str:
    return "yes" if np_hard else "no"


def _source_line(src: object) -> str:
    return f"**Source:** {_source_label(src)}\n"


def _notes_admonition(notes: object, kind: str = "note") -> str:
    """Render ``metadata.notes`` (expected: list[str]) as an admonition of
    type ``kind`` (e.g. ``note``, ``seealso``) containing a bulleted
    markdown list. Returns ``""`` when notes are missing or empty.
    """
    if not isinstance(notes, list) or not notes:
        return ""
    lines = ["```{" + kind + "}"]
    for item in notes:
        text = str(item).rstrip()
        if not text:
            continue
        # First line gets the bullet marker; continuation lines are
        # indented two spaces so they belong to the same list item.
        parts = text.split("\n")
        lines.append(f"- {parts[0]}")
        for cont in parts[1:]:
            lines.append(f"  {cont}" if cont else "")
    lines.append("```")
    return "\n".join(lines) + "\n"


def _map_table(entries: dict[str, Definition], header: str) -> str:
    rows = [f"| Name | {header} |", "|---|---|"]
    for name, d in entries.items():
        # Pipes inside the LaTeX would otherwise break the table column.
        formula = d.formulation.replace("|", r"\|")
        rows.append(f"| `{name}` | ${formula}$ |")
    return "\n".join(rows) + "\n"


def _reformulation_section(pid: int, reform: Reformulation) -> str:
    a, b = reform.a.path.name, reform.b.path.name
    a_ref = f"{{ref}}`{a} <{_formulation_target(pid, a)}>`"
    b_ref = f"{{ref}}`{b} <{_formulation_target(pid, b)}>`"
    badge = "valid" if reform.is_reformulation else "invalid"
    parts = [f"### {a_ref} → {b_ref} ({badge})\n"]

    pmap = reform.parameter_map
    note_block = _notes_admonition(pmap.metadata.get("notes"))
    if note_block:
        parts += [note_block, ""]
    if pmap.definitions:
        parts += [
            "**Definitions**\n",
            _map_table(pmap.definitions, f"Derived from `{a}`'s parameters"),
            "",
        ]
    parts += [
        "**Parameter map**\n",
        _map_table(pmap.parameters, f"Definition in terms of `{a}`"),
        "",
    ]
    return "\n".join(parts)


def _reformulations_section(pid: int, reforms: list[Reformulation]) -> str:
    if not reforms:
        return ""
    parts = [
        "## Reformulations\n",
        "Each entry below pairs two formulations of this problem, records whether "
        "the second is a reformulation of the first, and gives the parameter map "
        "carrying the first formulation's parameters to the second's.\n",
    ]
    parts += [_reformulation_section(pid, r) for r in reforms]
    return "\n".join(parts)


def _problem_page(pid: int, problem, reforms: list[Reformulation]) -> str:
    header = [
        "---",
        "tocdepth: 3",  # Don't show formulation subsections in the sidebar
        "---",
        "",
        f"# p{pid} | {problem.name}\n",
    ]
    src = problem.metadata.get("source")
    if src:
        label = _source_label(src)
        header += [
            "```{seealso}",
            f"This problem is sourced from {label}.",
            "```",
            "",
        ]
    note_block = _notes_admonition(problem.metadata.get("notes"))
    if note_block:
        header += [note_block, ""]
    header += [
        f"**NP-hard:** {_np_hard_label(problem.np_hard)}\n",
        "## Description\n",
        problem.description.strip() + "\n",
        "## Formulations\n",
    ]
    sections = [
        _formulation_section(pid, fid, f) for fid, f in problem.formulations.items()
    ]
    return (
        "\n".join(header) + "\n".join(sections) + _reformulations_section(pid, reforms)
    )


def _source_short(src: object) -> str:
    if not isinstance(src, dict):
        return str(src)
    cite = src.get("citekey")
    return f"{{cite:p}}`{cite}`" if cite else src.get("dataset", "?")


def _index_page(problems: dict[int, object]) -> str:
    lines = [
        "# Problems\n",
        "The table below enumerates every problem in FormulationBench and the "
        "source it was adapted from. Each problem page provides detailed information "
        "about the problem and every formulation of it. This documentation is "
        "automatically generated from the dataset to ensure it is up-to-date.\n",
        "| Problem | Name | NP-hard | Source |",
        "|---|---|---|---|",
    ]
    for pid, problem in problems.items():
        src = _source_short(problem.metadata.get("source", {}))
        hard = _np_hard_label(problem.np_hard)
        lines.append(f"| [p{pid}](p{pid}) | {problem.name} | {hard} | {src} |")
    lines += [
        "",
        "```{toctree}",
        ":hidden:",
        ":maxdepth: 1",
        "",
    ]
    for pid in problems:
        lines.append(f"p{pid}")
    lines += ["```", ""]
    return "\n".join(lines)


def _dataset_root(docs_dir: Path) -> Path:
    return docs_dir.parents[0] / "dataset"


def _write_if_changed(path: Path, content: str) -> None:
    """Write ``content`` to ``path`` only if different from current contents.

    Keeps mtime stable across no-op rebuilds so sphinx-autobuild's file
    watcher doesn't fire a rebuild on its own output.
    """
    if path.exists() and path.read_text() == content:
        return
    path.write_text(content)


def generate(docs_dir: Path) -> None:
    """Write generated problem pages under ``docs_dir/problems/``."""
    ds = Dataset(_dataset_root(docs_dir))
    out_dir = docs_dir / "problems"
    out_dir.mkdir(parents=True, exist_ok=True)
    by_problem: dict[int, list[Reformulation]] = {pid: [] for pid in ds.problems}
    for reform in ds.reformulations:
        by_problem[int(reform.a.problem.path.name[1:])].append(reform)
    for pid, problem in ds.problems.items():
        page = _problem_page(pid, problem, by_problem[pid])
        _write_if_changed(out_dir / f"p{pid}.md", page)
    _write_if_changed(out_dir / "index.md", _index_page(ds.problems))


def _on_builder_inited(app):  # type: ignore[no-untyped-def]
    generate(Path(app.confdir))


def setup(app):  # type: ignore[no-untyped-def]
    app.connect("builder-inited", _on_builder_inited)
    return {"version": "0.1", "parallel_read_safe": True, "parallel_write_safe": True}
