import json
import subprocess
from dataclasses import dataclass
from pathlib import Path

from ._codegen import generate_map
from .formulation import Formulation
from .models import ParameterMap


@dataclass(frozen=True)
class Reformulation:
    """A pair of MILP formulations with a reformulation label.

    Consists of two MILP formulations ``a`` and ``b`` and a boolean ``is_reformulation``
    label indicating whether ``b`` is a reformulation of ``a``. The formal definition
    of *reformulation* is given in :ref:`reformulation-definition`. Positive entries
    (``is_reformulation=True``) are accompanied by a Lean 4 proof whose path is
    accessible via the ``lean_proof_path`` attribute; negative entries have no proof
    and ``lean_proof_path`` resolves to ``None``.

    Attributes
    ----------
    a : Formulation
        The base formulation.
    b : Formulation
        The reformulation candidate.
    is_reformulation : bool
        ``True`` iff ``b`` is a *reformulation* of ``a``.
    lean_proof_path : pathlib.Path or None
        For positive entries, the path to the accompanying Lean 4 proof file. For
        negative entries, ``None`` since no proof exists.
    map_path : pathlib.Path
        Path to this pair's ``map.json``, which states how each parameter of ``b``
        is computed from the parameters of ``a``.
    parameter_map : ParameterMap or None
        The loaded ``map.json``, or ``None`` for a pair that has none.

    Examples
    --------

    Formulation ``b`` of :doc:`/problems/p12` is a reformulation of formulation ``a``::

        >>> from formulation_bench import Dataset
        >>> ds = Dataset("dataset")
        >>> reform = ds.reformulations[73]  # corresponds to p12.a -> p12.b
        >>> reform.a.problem.name
        'Traveling Salesman Problem (TSP)'
        >>> reform.b.problem.name
        'Traveling Salesman Problem (TSP)'
        >>> reform.b.constraints[-1].description  # cutting plane added by p12.b
        'Depot-Exit Position Bound (EC1)...'
        >>> reform.is_reformulation
        True
    """

    a: Formulation
    b: Formulation
    is_reformulation: bool

    @property
    def _reformulation_dir(self) -> Path:
        problem_dir = self.a.problem.path
        return problem_dir.parent.parent / "reformulations" / problem_dir.name

    @property
    def lean_proof_path(self) -> Path | None:
        if not self.is_reformulation:
            return None
        return self._reformulation_dir / f"{self.a.path.name}_{self.b.path.name}.lean"

    @property
    def map_path(self) -> Path:
        pair = f"{self.a.path.name}_{self.b.path.name}"
        return self._reformulation_dir / pair / "map.json"

    @property
    def parameter_map(self) -> ParameterMap | None:
        if not self.map_path.exists():
            return None
        return ParameterMap.from_dict(json.loads(self.map_path.read_text()))

    def gen_map_py(self) -> str:
        """Generate a Python script computing ``b``'s parameters from ``a``'s.

        The script is generated from the ``python`` code snippets of this pair's
        ``map.json``: its definitions first, then one statement per parameter of
        ``b``, in declaration order. It is the parameter-map counterpart of the
        per-formulation ``gen_params.py``, and composing the two must agree ---
        running ``a``'s ``gen_params.py`` and then this script yields the same
        parameters as running ``b``'s ``gen_params.py``.

        The resulting script takes the path to ``a``'s ``parameters.json`` and
        the path to write ``b``'s as positional arguments.

        Raises
        ------
        FileNotFoundError
            If this pair has no ``map.json``.

        Examples
        --------

        Generate the parameter-map script for the ``a`` to ``b`` pair of
        :doc:`/problems/p1`, whose parameters are a renaming::

            >>> from formulation_bench import Dataset
            >>> ds = Dataset("dataset")
            >>> reform = ds.reformulations[0]  # corresponds to p1.a -> p1.b
            >>> script = reform.gen_map_py()
            >>> print(script)
            import argparse
            import json
            <BLANKLINE>
            <BLANKLINE>
            def main(params_path: str, output_path: str) -> None:
                with open(params_path, "r") as f:
                    data = json.load(f)
            <BLANKLINE>
                # Source Parameters
                CashMachineProcessingRate = data["CashMachineProcessingRate"]
                ...
                # Parameter Map
                A = CashMachineProcessingRate
                ...

        """
        if self.parameter_map is None:
            raise FileNotFoundError(f"no parameter map at {self.map_path}")
        return generate_map(self)

    def run_map(
        self,
        input_path: str | Path | None = None,
        output_path: str | Path | None = None,
    ) -> None:
        """Write this pair's ``map.py`` and run it.

        The script generated by :meth:`gen_map_py` is written to ``map.py``
        alongside the pair's ``map.json``, then applied to ``a``'s parameters to
        produce ``b``'s.

        Parameters
        ----------
        input_path : str or pathlib.Path, optional
            Path to a ``parameters.json`` holding formulation ``a``'s parameters.
            Defaults to ``parameters.json`` in ``a``'s formulation directory,
            which :meth:`Formulation.run_gen_params` writes.
        output_path : str or pathlib.Path, optional
            Path to write the mapped parameters. Defaults to ``parameters.json``
            alongside this pair's ``map.json``.

        Raises
        ------
        FileNotFoundError
            If this pair has no ``map.json``.

        Examples
        --------

        Map formulation ``a``'s parameters to formulation ``b``'s for
        :doc:`/problems/p1`::

            >>> import json
            >>> from formulation_bench import Dataset
            >>> ds = Dataset("dataset")
            >>> reform = ds.reformulations[0]  # corresponds to p1.a -> p1.b

            >>> reform.a.run_gen_params()
            >>> reform.run_map()
            >>> params = json.load(open(reform.map_path.parent / "parameters.json"))
            >>> params["A"]  # b's name for "CashMachineProcessingRate"
            20

        """
        script = self.map_path.parent / "map.py"
        script.write_text(self.gen_map_py())
        if input_path is None:
            input_path = self.a.path / "parameters.json"
        if output_path is None:
            output_path = self.map_path.parent / "parameters.json"
        subprocess.run(
            ["python", str(script), str(input_path), str(output_path)], check=True
        )
