# formulation-bench Agent Guide

`formulation-bench` is a Python package for loading and working with the
**FormulationBench** dataset: a collection of optimization problems, MILP
formulations, and Lean 4 reformulation proofs.

## Repository

This repository is the source of truth for the `formulation-bench` package
(published to PyPI) and its documentation (published to Read the Docs). It
was extracted from the [FLARE
monorepo](https://github.com/henryrobbins/flare), where the package
previously lived as a uv workspace member under
`packages/formulation_bench/`.

The dataset lives in this repository under `dataset/`, and the docs build
reads from it directly. The dataset is also published as a GitHub release
tarball; `download_dataset()` fetches it from the releases of this repo.

## Tooling

- **uv** — environment management
- **ruff** — linting and formatting (`E`, `F`, `I`, `UP`; line length 88)
- **mypy** — type-checking in `strict` mode
- **pytest** — tests, including `--doctest-modules` on the source tree
- **Sphinx** (with `myst-parser`, `furo`, `numpydoc`,
  `sphinx-autodoc-typehints`) — docs, hosted on Read the Docs
- **Jinja2** — runtime templating (the package's only runtime dep)

All common commands are wrapped in the `Makefile`. Run `make help` from
the repository root for the list.

## File structure

```
formulation-bench/
├── .claude/
│   ├── agents/              # MILP formulator / autoformalizer / reviewer
│   └── skills/              # Lean MILP formulation + reformulation standards
├── src/formulation_bench/   # the package
│   ├── dataset.py           # top-level Dataset loader
│   ├── problem.py           # Problem model
│   ├── formulation.py       # Formulation model
│   ├── reformulation.py     # Reformulation model
│   ├── models.py            # shared data models (Parameter, Variable, ...)
│   ├── download.py          # dataset download helpers
│   ├── _codegen.py          # Python code generation
│   ├── _render.py           # Jinja rendering helpers
│   └── templates/           # Jinja templates
├── dataset/                 # the FormulationBench dataset
├── scripts/                 # dataset validation utilities
├── tests/                   # pytest suite
├── docs/                    # Sphinx docs (published to Read the Docs)
│   ├── conf.py
│   ├── index.md
│   ├── installation.md
│   ├── user_guide/
│   ├── problems/            # per-problem pages (generated from dataset/)
│   ├── lean/
│   ├── api/
│   ├── schema.md
│   └── serve.sh             # sphinx-autobuild wrapper
├── Makefile
├── pyproject.toml
└── README.md
```

## Tests

```bash
make test
```

Pytest is configured to collect from both `tests/` and
`src/formulation_bench/` (the latter for `--doctest-modules`), so
docstring examples are part of the suite — keep them runnable.

Some doctests instantiate `Dataset("dataset")` with a relative path; this
resolves against the `dataset/` directory at the repository root, so run
the tests from there.

## Coverage

```bash
make cov        # pytest with coverage; writes htmlcov/ and coverage.xml
make cov-open   # open the HTML report in a browser
make cov-clean  # remove coverage artifacts
```

CI uploads `coverage.xml` to
[Codecov](https://codecov.io/gh/henryrobbins/formulation-bench).

## Docs

Build once:

```bash
make docs
```

Live-reload while editing (watches both `docs/` and `dataset/` so
per-problem pages regenerate when dataset JSON changes):

```bash
make docs-serve
```

Both targets pull in the `docs` extra automatically. Sphinx is
configured with `fail_on_warning: true` on Read the Docs, so `make
docs` also runs with `-W` locally.

## Lint, format, type-check

```bash
make lint        # ruff check
make format      # ruff format + ruff check --fix
make typecheck   # mypy (strict)
make check       # all of the above plus tests
```

mypy is strict and scoped to `src/formulation_bench` — new code needs
full annotations. Ruff's selected rule groups are `E`, `F`, `I`, `UP`;
let `make format` handle import ordering and modern-syntax rewrites.

## Common Workflows

The repo provides a set of skills and agents for working with the dataset.
The agents live in `.claude/agents/`; the standards they follow are the
skills in `.claude/skills/`. All three agents also use the `lean4:lean4`
skill and the `lean-lsp` MCP server configured in `.mcp.json`.

**Generate a Lean MILP formulation**

1. Identify the relevant source file(s) to read. E.g., the relevant source
   files for problem 1, formulation e (p1.e) are the problem files in
   `dataset/problems/p1` and the formulation files in
   `dataset/problems/p1/formulations/e`. If the user requests generating
   formulations for a problem, generate all of the problem's formulations.
2. The output file(s) will be `Formulation.lean` in each formulation's
   subdirectory. E.g., the formulation for p1.e goes in
   `dataset/problems/p1/formulations/e/Formulation.lean`.
3. Invoke the `milp-formulator` agent with the identified source/output. If
   generating multiple formulations, invoke multiple agents in parallel.

**Generate Lean MILP reformulation proof**

1. Identify the relevant source file(s) to read. At minimum, read each
   MILP's `Formulation.lean` file. E.g., for proving p1.b is a reformulation
   of p1.a, read the problem files in `dataset/problems/p1` and the
   formulation files in `dataset/problems/p1/formulations/a|b`. If a
   formulation subdirectory does not yet contain `Formulation.lean`, follow
   the steps above to generate it.
2. The output file for proving formulation b is a reformulation of
   formulation a (for problem X) is `dataset/reformulations/pX/a_b.lean`.
3. Invoke the `milp-reformulation-autoformalizer` agent with the identified
   source/output. If generating multiple proofs, invoke multiple agents in
   parallel.

**Review existing Lean MILP formulations or reformulation proofs**

1. Identify the relevant file(s) to read: problem files, formulation files,
   `Formulation.lean`, and `dataset/reformulations/pX/a_b.lean`.
2. Invoke the `milp-reviewer` agent pointing to the relevant file locations.
   If reviewing multiple files, invoke multiple agents in parallel.
