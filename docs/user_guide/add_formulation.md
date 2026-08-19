# Adding a new formulation

A MILP formulation must be added to an existing optimization problem. To create a new problem, follow the instructions in {doc}`add_problem`.

Adding a new formulation consists of writing the following files:
- JSON file expressing every component of the formulation (e.g., variables, constraints, objective) in natural-language, math (LaTeX), and code (GurobiPy). 
- Parameter generation script that translates problem data into parameter input for the formulation.
- Lean 4 encoding following the {ref}`Formulation definition <formulation-definition>`

By convention, formulation names are single letter labels (e.g., `a`, `b`). Pick the next free label `x` for `pN` and create `problems/pN/formulations/x/`. Next, populate the directory with the required files as outlined below.

## JSON File

The `formulation.json` file is the core object defining the formulation. See {ref}`formulation-directory` for the full schema. In order for {meth}`Formulation.gen_solve_py() <formulation_bench.formulation.Formulation.gen_solve_py>` to generate a working solver script, all `assumptions` and `definitions` must contain `code.python` and all `constraints` and the `objective` must contain `code.gurobipy`.

:::{tip}
Reading raw LaTeX while editing the JSON file can be cumbersome. The {doc}`/problems/index` documentation is automatically generated from the dataset and provides a nice way to view a rendering of the formulation while editing. If you're working in the {github}`source repository </>`, you can run `make docs-serve` from the repository root to host the docs with live-reload on `http://127.0.0.1:8000`.
:::

:::{dropdown} `problems/p12/formulations/a/formulation.json`
:icon: code
```{literalinclude} ../../dataset/problems/p12/formulations/a/formulation.json
:language: json
```
:::

## Parameter Generation Script

The parameter generation script `gen_params.py` reads the problem data instance defined in `data.json` and transforms it into the parameter input for the formulation (`parameters.json`). This allows the dataset to have a single source of data per problem. The script should accept the input `data.json` and output `parameters.json` paths as positional arguments.

:::{dropdown} `problems/p1/formulations/b/gen_params.py`
:icon: code
```{literalinclude} ../../dataset/problems/p1/formulations/b/gen_params.py
:language: python
```
:::

## Lean 4 Encoding

Each formulation must have a Lean 4 encoding in `Formulation.lean` following the {ref}`Formulation definition <formulation-definition>`. This file should import `MILPFormulation` from `Common.lean` and define `formulation : MILPFormulation` inside the `PN.x` namespace where `N` is the problem identifier and `x` is the formulation identifier.

The {github}`GitHub repo </>` ships with the `milp-formulator` agent which uses the `lean-milp-formulation` agent skill from {mf}`FLARE </skills.html#lean-milp-formulation>` to automatically generate `Formulation.lean`.

:::{dropdown} `problems/p1/formulations/b/Formulation.lean`
:icon: code
```{literalinclude} ../../dataset/problems/p1/formulations/b/Formulation.lean
:language: lean
```
:::

## Registering Reformulation Pairs

If your new formulation forms a (positive or negative) reformulation
pair with another formulation of the same problem, add an entry to the `reformulations` field in `dataset.json`:

```json
{
  "a": {"problem": 21, "formulation": "a"},
  "b": {"problem": 21, "formulation": "b"},
  "reformulation": true
}
```

Every reformulation pair needs a parameter map in `reformulations/pN/x_y/map.json`, stating how parameters of `x` map to parameters of `y`. See {ref}`parameter-map` for the full schema. Each entry carries a LaTeX `formulation` and a `code.python` snippet;
the latter is what {meth}`Reformulation.gen_map_py()
<formulation_bench.reformulation.Reformulation.gen_map_py>` assembles into a
runnable script. The mapping should agree with each formulations' `gen_params.py` script.

::::{dropdown} `reformulations/p1/a_b/map.json`
:icon: code
```{literalinclude} ../../dataset/reformulations/p1/a_b/map.json
:language: json
```
::::

For positive pairs, create a Lean proof following the {ref}`Reformulation definition <reformulation-definition>`. The parameter mapping defined in `paramMap` **must** agree with the one defined in the `map.json` file.

Put the Lean proof in `reformulations/pN/x_y/Reformulation.lean` where `N` is the common problem and the proof shows `y` is a reformulation of `x`. The file should import `Common` and both formulations:

```lean
import Common
import problems.pN.formulations.x.Formulation
import problems.pN.formulations.y.Formulation
```

The definition `xYReformulation : MILPReformulation PN.x.formulation PN.y.formulation` should be defined within the `PN` namespace.

The {github}`GitHub repo </>` ships with the `milp-reformulation-autoformalizer` agent which uses the `lean-milp-reformulation` agent skill from {mf}`FLARE </skills.html#lean-milp-reformulation>` to automatically generate the Lean proof.

:::{dropdown} `reformulations/p1/a_b/Reformulation.lean`
:icon: code
```{literalinclude} ../../dataset/reformulations/p1/a_b/Reformulation.lean
:language: lean
```
:::

## Validating

The dataset test suite checks that the `solve.py` script generated by {meth}`Formulation.gen_solve_py() <formulation_bench.formulation.Formulation.gen_solve_py>` achieves the ground-truth optimal solution specified in the problem's `solution.json` file, and that the recorded variable values are feasible. This also verifies that `formulation.json` is well-structured.

```bash
pytest tests/dataset -m dataset --problems N  # run on problem pN
```

Additionally, follow the instructions in {doc}`/user_guide/build_lean` to compile `Formulation.lean` and any reformulation proof Lean files.
