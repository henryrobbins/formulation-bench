---
name: new-formulation
description: >
  Procedure for adding a new MILP formulation to an existing FormulationBench
  problem. Use when creating/editing `dataset/problems/pN/formulations/x/`.
---

# Adding a New Formulation

The authoritative guide for adding a formulation is `docs/user_guide/add_formulation.md`.
**Read it first.** Next, reference `docs/schema.md` to understand the dataset
**schema**, especially the Formulation Directory section. This skill provides
additional guidance and conventions.

Use the `new-problem` skill to add a new problem before adding a formulation for it.

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

When applicable, you can reference the citation in the formulation JSON `metadata.notes`
field or description fields as `{cite:t}`citekey``.

## Validation

```bash
python scripts/check_citations.py            # citekeys resolve in ref.bib
python scripts/validate_solve.py -p N        # once pN has a formulation
make docs                                    # -W; the problem page must build
```

Ensure any added Lean files compile; run the following from the repository root:

```bash
lake build problems.pN.formulations.x.Formulation
lake build reformulations.pN.x_y.Reformulation
```

All of these must pass before the formulation is done.

## `metadata.notes`

Use formulation notes for concise context that helps a reader understand why this
formulation exists or how it relates to the problem, source, or sibling
formulations.

**DO:**

- DO document assumptions or deviations that apply only to this formulation.
- DO use a short, high-level note when the formulation's relationship to the
  source or another formulation would not otherwise be clear. Examples include
  a variable-renaming transformation, aggregation versus disaggregation, a
  base-10 substitution, or the source/version of an acceleration cut.
- DO use the `{cite:t}`citekey`` syntax when a note mentions the source by
  name.
- DO keep notes concise and focused on information not apparent from the
  structured formulation.

**DO NOT:**

- DO NOT duplicate the formulation's variables, constraints, objective, or cut
  behavior in a note. Put explanatory detail about a specific constraint in
  that constraint's `description` instead.
- DO NOT use notes as a full natural-language summary of the formulation.
- DO NOT document deviations from the source used in _every_ formulation;
  document these in the `metadata.notes` field of the problem JSON file instead.
- DO NOT include a note that solely documents the source of the formulation, unless
  its provenance helps distinguish this formulation from related formulations.
- DO NOT describe the formulation parameters and/or `gen_params.py`

## `explicit` field in `formulation.json`

**DO:**

- DO set `explicit: true` for constraints that are explicitly stated in the source.
- DO set `explicit: true` for modifications to the source formulation.
- DO set `explicit: false` for assumptions required to prove reformulation validity
  that are NOT explicit in the source (e.g., non-negativity, triangle inequality, etc.).

**DO NOT:**

- DO NOT set `explicit: false` for modifications to the source solely required to
  satisfy the stricter definition of reformulation defined in FormulationBench.

## Miscellaneous

- Use LaTeX math mode for math symbols in `description.md` and both
  `*.description` and `metadata.notes` fields in `formulation.json`.
