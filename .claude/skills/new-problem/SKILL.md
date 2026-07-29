---
name: new-problem
description: >
  Procedure for adding a new optimization problem to the FormulationBench
  dataset. Use when creating/editing a `dataset/problems/pN/` directory.
---

# Adding a New Problem

The authoritative guide for adding a problem is `docs/user_guide/add_problem.md`.
**Read it first.** Next, reference `docs/schema.md` to understand the dataset
**schema**, especially the Problem Directory section. This skill provides
additional guidance and conventions.

Adding at least one formulation is what makes the problem usable; a problem with
no formulations is incomplete. Once you've added the problem, use the
`new-formulation` skill to add formulations.

## Citations

The source of official FormulationBench problems must be properly cited. Add a
BibTeX entry to `dataset/ref.bib` (if not already present) and include the
`citekey` in the `metadata.source.citekey` field of `formulation.json`. For example:

```
"metadata": {
      "source": {
          "citekey": "ferchtandiker2025"
      },
  }
```

When applicable, you can reference the citation in the problem JSON `metadata.notes`
field as `{cite:t}`citekey``.

## Validation

```bash
python scripts/check_citations.py            # citekeys resolve in ref.bib
python scripts/validate_solve.py -p N        # once pN has a formulation
make docs                                    # -W; the problem page must build
```

`validate_solve.py` needs at least one formulation, so it is the last check
to come green. Run `make docs` regardless.

## `metadata.notes`

**DO:**

- DO document any deviation from the source used in _every_ formulation.
- DO document any assumptions added to the problem that are not in the source.
- DO use the `{cite:t}`citekey`` syntax to reference the source in notes.
- DO keep notes concise

**DO NOT:**

- DO NOT include a note that solely documents the source of the problem, unless
  it adds additional information (e.g., a citation referenced in the source).
- DO NOT include a summary of the problem's formulations.
- DO NOT describe the problem parameters and/or `gen_params.py`

## Miscellaneous

- Use LaTeX math mode for math symbols in `description.md` and both
  `parameters.description` and `metadata.notes` fields in `problem.json`.
