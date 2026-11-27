"""Regression checks for the lattice certificate and custom Ewald configurations."""
import io
import json
import os
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from dataclasses import replace
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch

import numpy as np
from flint import arb

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "programs"))
import lattice
from bccnum import ewald_cert, ewald_float, lattice_cert, structures


class TailTests(unittest.TestCase):
    def family(self, first, second):
        matrix = [[lattice_cert.Jet.const(0) for _ in range(3)] for _ in range(3)]
        matrix[2][2].g[-1] = first
        matrix[2][2].h[-1][-1] = second
        return lattice_cert._family_tail(matrix, arb(3), 6, arb.pi())

    def test_zero_crossing_bounds_nonzero_endpoints(self):
        wide = arb(0, 1)
        for first, second in ((wide, arb(0)), (arb(0), wide)):
            with self.subTest(first=first, second=second):
                upper = self.family(first, second)
                point = self.family(arb(1) if first.contains(1) else first, arb(1) if second.contains(1) else second)
                self.assertTrue(upper.is_finite() and upper >= point and point > 0)

    def test_nonfinite_derivative_in_either_maximum_fails(self):
        for bad in (arb("nan"), arb.pos_inf()):
            for first, second in ((bad, arb(1)), (arb(1), bad)):
                with self.subTest(first=first, second=second), self.assertRaises(ArithmeticError):
                    self.family(first, second)


class LatticeDriverTests(unittest.TestCase):
    def test_root_and_partial_failures_reach_exit_status(self):
        with tempfile.TemporaryDirectory() as tmp:
            lo, hi = lattice.root_box()
            for mode, short_root, missing, expected in (("all", False, 0, 0), ("all", True, 0, 1),
                                                        ("boxes", True, 0, 1), ("all", False, 1, 1),
                                                        ("strain", False, 1, 1)):
                root = ([1.0, *lo[1:]] if short_root else lo, hi)
                with (self.subTest(mode=mode, short=short_root, unresolved=missing),
                      patch.dict(os.environ, BCC_RESULTS_DIR=tmp), patch.dict(lattice.PARAMS, grid=1),
                      patch.object(lattice, "Pool") as pool, patch.object(lattice, "root_box", return_value=root),
                      patch.object(lattice, "setup", return_value={}), patch.object(lattice, "strain_regions", return_value={}),
                      patch.object(lattice, "strain_certificate", return_value={"unresolved": missing}),
                      redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO())):
                    workers = pool.return_value.__enter__.return_value
                    workers.map.return_value = [{"all_pd": True, "C_range_ok": True}, {"all_pd": True}]
                    workers.imap.return_value = [("R", None)]
                    self.assertEqual(lattice.main([mode]), expected)
                    if mode == "all":
                        data = json.loads((Path(tmp) / "lattice.json").read_bytes())["results"]
                        self.assertEqual(data["certified"], expected == 0)
                        self.assertEqual(data["boxes"]["root_contains_proof_root_box"], not short_root)


class ProvenanceTests(unittest.TestCase):
    def test_result_written_after_a_change_of_an_input_fails(self):
        from bccnum import provenance
        with tempfile.TemporaryDirectory() as tmp, patch.dict(os.environ, BCC_RESULTS_DIR=tmp):
            source = Path(tmp) / "input.json"
            source.write_bytes(b"{}")

            def provenance_of(name):
                return json.loads((Path(tmp) / f"{name}.json").read_bytes())["provenance"]

            run = provenance.Run(__file__, {}, "cert", inputs={"input.json": (str(source), None)})
            run.write("unchanged", {})
            self.assertTrue(provenance_of("unchanged")["unchanged_at_end"])
            self.assertEqual(provenance_of("unchanged")["inputs_sha256"]["input.json"],
                             provenance.sha256_file(str(source)))
            for case in ("changed during the run", "read bytes other than the file's"):
                with self.subTest(case=case):
                    digest = "0" * 64 if case.startswith("read") else None
                    run = provenance.Run(__file__, {}, "cert", inputs={"input.json": (str(source), digest)})
                    if case.startswith("changed"):
                        source.write_bytes(source.read_bytes() + b" ")
                    with self.assertRaises(RuntimeError):
                        run.write("changed", {})
                    self.assertFalse(provenance_of("changed")["unchanged_at_end"])


class ConfigurationTests(unittest.TestCase):
    def test_periodic_collisions_rejected_before_aggregation(self):
        for other in ((0, 0, 0), (2, -4, 6)):
            with self.subTest(other=other):
                with self.assertRaisesRegex(ValueError, "coincident"):
                    structures.periodic_configuration("collision", 2, [(0, 0, 0), other], [1, -1])
                structure = replace(structures.sc(), frac=((0, 0, 0), other), charges=(1, -1))
                with self.assertRaisesRegex(ValueError, "coincident"):
                    ewald_cert.ewald_energy(structure, 1, 4, 4)
                with self.assertRaisesRegex(ValueError, "coincident"):
                    ewald_float.ewald_energy_float(np.eye(3), [(0, 0, 0), other], [1, -1], 1, 3, 3)

    def test_exact_shell_retains_close_pair(self):
        distance = Fraction(1, 2**20)
        s = structures.periodic_configuration("pair", 1, [(0, 0, 0), (1 - distance, 0, 0)])
        denominator, shells, _, _ = ewald_cert.real_space_shells(s, distance**2)
        self.assertEqual({Fraction(n, denominator): w for n, w in shells.items()}, {distance**2: 2})

    def test_fractional_input_preserves_site_identity_before_ws_scaling(self):
        start = Fraction(1, 8)
        with self.assertRaisesRegex(ValueError, "coincident"):
            ewald_float.ocp_energy_ws_float(np.eye(3), [(start, 0, 0), (1 + start, 0, 0)])
        distance = Fraction(1, 2**60)
        energy = ewald_float.ocp_energy_ws_float(np.eye(3), [(start, 0, 0), (1 + start + distance, 0, 0)])
        scale = ewald_float.ws_scale(np.eye(3), 2)
        self.assertAlmostEqual(2 * scale * float(distance) * energy, 1.0, places=13)

    def test_float_keeps_close_pairs_on_both_sides_of_period(self):
        distance = 2.0**-55
        for first in (0, 1, -11):
            with self.subTest(first=first):
                energy = ewald_float.ewald_energy_float(np.eye(3), [(first, 0, 0), (distance, 0, 0)],
                                                       [1, 1], 1, 3, 4)
                self.assertAlmostEqual(distance * energy, 1.0, places=13)
