# FormulationBench

:::{note}
FormulationBench was introduced by *{paper}`FLARE: Verifying MILP Reformulations with LLM-Based Formal Proof Synthesis </>`*
:::

FormulationBench is a dataset of **20** optimization problems (see {doc}`problems/index`) with **109** MILP formulations. Each formulation includes a description, LaTeX formulation, GurobiPy code, and Lean encoding.

The dataset also includes **89** reformulation pairs (63 positive and 26 negative examples), with a machine-checked Lean 4 reformulation proof for every positive pair.

The `formulation-bench` Python package is the ideal interface for working with the dataset. See below for installation instructions, user guides, and the API reference.

```{toctree}
:maxdepth: 2
:caption: Contents

installation
user_guide/index
problems/index
schema
definitions
api/index
citations
```
