"""Regression checks for certificate inputs, controls and the refiner."""
import io
import json
import os
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "cover"))
import check_receipt
import record_controls
from cover_verifier import controls, defect, gain, refine, rules, verify


class OffsetTests(unittest.TestCase):
    basis = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
    shift = (0, 0, 0)

    def test_registered_half_class(self):
        f = (Fraction(3, 2), Fraction(-1, 2), Fraction(1, 2))
        self.assertEqual(defect.Registration(self.basis, f, self.shift).f0, f)
        with self.assertRaises(ValueError):
            defect.Registration(self.basis, ("1/2", 0, 0), self.shift)

    def test_offset_dimension_through_every_leaf(self):
        box = controls.BCC_BOX
        for f in ([], ["1/2", "1/2"], [0, 0, 0, "1/2"], ["1/2"] * 4):
            registration = [self.basis, f, self.shift]
            leaves = [["D1", "support", registration], ["D3", "support", registration, [0, 0, 0, 1], 1],
                      ["AG", f, self.shift], ["AS", f, self.shift, "support"], ["AP", f, self.shift],
                      ["AC", f, self.shift], ["AC", ["1/2"] * 3, self.shift, registration]]
            for leaf in leaves:
                with self.subTest(rule=leaf[0], f=f):
                    with self.assertRaisesRegex((ValueError, rules.Rejected), "three coordinates"):
                        verify.check_leaf(box, leaf, lambda *_: None)
            with self.assertRaisesRegex(ValueError, "three coordinates"):
                gain.GainForm(box[0][:5], box[1][:5], f)


class ControlTests(unittest.TestCase):
    def test_mutation_needs_original_acceptance_and_changed_rejection(self):
        with tempfile.TemporaryDirectory() as tmp:
            stage = Path(tmp) / "stage01.jsonl"
            stage.touch()
            report = Path(tmp) / "report.json"
            leaf = (stage, {"id": "sample"}, 0, controls.BCC_BOX, ["N", "full", [1, 0, 0]], {})
            for orig, changed, expected in (("accepted", "rejected", 0), ("rejected", "rejected", 1),
                                            ("accepted", "accepted", 1)):
                with (self.subTest(orig=orig, changed=changed), redirect_stdout(io.StringIO()),
                      patch.object(controls, "find_leaf", side_effect=lambda _, rule: leaf if rule == "N" else None),
                      patch.object(controls, "run_leaf", side_effect=[(orig, "original"), (changed, "changed")]),
                      patch.object(controls, "battery_controls"), patch.object(controls, "completeness_controls")):
                    status = controls.main([tmp, "--allow-missing", "--report", str(report)])
                    self.assertEqual(status, expected)
                    mutation, = [r for r in json.loads(report.read_bytes())["controls"]
                                 if isinstance(r["detail"], dict) and "unchanged_leaf" in r["detail"]]
                    self.assertEqual(mutation["detail"]["unchanged_leaf"][0], orig)
                    self.assertEqual(mutation["detail"]["changed_outcome"], changed)


class RecordControlsTests(unittest.TestCase):
    def test_report_records_what_the_controls_ran_on(self):
        with tempfile.TemporaryDirectory() as tmp:
            cert = Path(tmp) / "certificate"
            cert.mkdir()
            stage = cert / "stage01.jsonl"
            stage.write_bytes(b'{"format": "cover-certificate-1"}\n')
            report = Path(tmp) / "controls.json"

            def controls_run(argv, change=False):
                Path(argv[argv.index("--report") + 1]).write_text(json.dumps({"bits": 128, "controls": []}))
                if change:
                    stage.write_bytes(stage.read_bytes() + b"\n")
                return 0

            for change, expected in ((False, 0), (True, 1)):
                with (self.subTest(change=change), redirect_stdout(io.StringIO()),
                      patch.object(controls, "main", side_effect=lambda argv: controls_run(argv, change))):
                    self.assertEqual(record_controls.main([str(cert), "--report", str(report)]), expected)
                    data = json.loads(report.read_bytes())
                    provenance = data["provenance"]
                    self.assertEqual(provenance["unchanged"], not change)
                    self.assertEqual(provenance["before"]["verifier"], verify.source_digests())
                    self.assertEqual(set(provenance["before"]["inputs"]), {stage.name})
                    self.assertEqual(provenance["before"]["inputs"] == provenance["after"]["inputs"], not change)
                    self.assertEqual(data["controls"], [])


class ReceiptTests(unittest.TestCase):
    recorded = Path(check_receipt.__file__).parent / "run" / "receipt.json"

    @unittest.skipUnless(recorded.exists(), "no recorded receipt")
    def test_recorded_receipt_matches_this_verifier(self):
        with redirect_stdout(io.StringIO()):
            self.assertEqual(check_receipt.main([self.recorded]), 0)
            self.assertEqual(check_receipt.main([self.recorded, self.recorded]), 0)

    @unittest.skipUnless(recorded.exists(), "no recorded receipt")
    def test_other_verifier_or_failed_run_is_not_accepted(self):
        receipt = json.loads(self.recorded.read_text(encoding="utf-8"))
        with tempfile.TemporaryDirectory() as tmp:
            for change in ("verifier", "at_end", "result", "count"):
                changed = json.loads(json.dumps(receipt))
                if change == "verifier":
                    changed["verifier"]["verify.py"] = "0" * 64
                elif change == "at_end":
                    changed["inputs_at_end"] = dict(changed["inputs"], **{next(iter(changed["inputs"])): "0" * 64})
                elif change == "result":
                    changed["result"] = "PASS OF AN INCOMPLETE RUN"
                else:
                    stage = next(s for s in changed["counts"] if changed["counts"][s])
                    rule = next(iter(changed["counts"][stage]))
                    changed["counts"][stage][rule] += 1
                path = Path(tmp) / f"{change}.json"
                path.write_text(json.dumps(changed), encoding="utf-8")
                with self.subTest(change=change), redirect_stdout(io.StringIO()):
                    self.assertEqual(check_receipt.main([path]), 1)

    @unittest.skipUnless(recorded.exists(), "no recorded receipt")
    def test_recorded_receipt_of_another_verifier_is_not_accepted(self):
        other = json.loads(self.recorded.read_text(encoding="utf-8"))
        other["verifier"]["verify.py"] = other["verifier_at_end"]["verify.py"] = "0" * 64
        with tempfile.TemporaryDirectory() as tmp:
            reference = Path(tmp) / "receipt.json"
            reference.write_text(json.dumps(other), encoding="utf-8")
            with patch.object(check_receipt, "RECORDED", reference), redirect_stdout(io.StringIO()):
                self.assertEqual(check_receipt.main([self.recorded]), 1)
                self.assertEqual(check_receipt.main([reference]), 1)
                self.assertEqual(check_receipt.main([reference, reference]), 0)


class ChangeDuringRunTests(unittest.TestCase):
    def test_verifier_fails_when_the_certificate_or_its_code_changes_during_the_run(self):
        with tempfile.TemporaryDirectory() as tmp:
            cert = Path(tmp) / "certificate"
            cert.mkdir()
            box = [[str(x) for x in end] for end in verify.boxes.K_BOX]
            records = [{"format": verify.FORMAT}, {"t": "piece", "id": "root", "box": box, "tree": ".",
                                                   "leaves": [["N", "full", [1, 0, 0]]]}, {"t": "end", "held": 0}]
            (cert / "stage01.jsonl").write_text("".join(json.dumps(r) + "\n" for r in records), encoding="utf-8")
            receipt = Path(tmp) / "receipt.json"
            args = [str(cert), "--skip-inequalities", "--receipt", str(receipt)]
            with redirect_stdout(io.StringIO()):
                self.assertEqual(verify.main(args), 0)
                data = json.loads(receipt.read_bytes())
                self.assertEqual(data["result"], "PASS OF AN INCOMPLETE RUN")
                self.assertEqual((data["verifier_at_end"], data["inputs_at_end"]), (data["verifier"], data["inputs"]))
                for name in ("input_digests", "source_digests"):
                    real = getattr(verify, name)
                    calls = []

                    def changing(*a, real=real, calls=calls):
                        calls.append(1)
                        d = real(*a)
                        return d if len(calls) == 1 else dict(d, changed="0" * 64)

                    with self.subTest(changed=name), patch.object(verify, name, side_effect=changing):
                        self.assertEqual(verify.main(args), 1)
                        self.assertEqual(json.loads(receipt.read_bytes())["result"], "FAIL")


class RefinerTests(unittest.TestCase):
    def test_rejected_stage_survives_in_place_refinement_cli(self):
        cover = Path(verify.__file__).resolve().parents[1]
        with tempfile.TemporaryDirectory() as tmp:
            cert = Path(tmp) / "certificate"
            cert.mkdir()
            stage = cert / "stage01.jsonl"
            box = [[str(x) for x in end] for end in verify.boxes.K_BOX]
            records = [{"format": verify.FORMAT},
                       {"t": "piece", "id": "root", "box": box, "tree": ".",
                        "leaves": [["AG", [0, 0, 0, "1/2"], [0, 0, 0]]]},
                       {"t": "end", "held": 0}]
            original = "".join(json.dumps(r) + "\n" for r in records).encode()
            stage.write_bytes(original)
            receipt = Path(tmp) / "receipt.json"
            verifier = subprocess.run([sys.executable, "-B", "-m", "cover_verifier.verify", str(cert),
                                       "--workers", "1", "--receipt", str(receipt)], cwd=cover, capture_output=True)
            self.assertEqual(verifier.returncode, 1, verifier.stderr)
            report = json.loads(receipt.read_bytes())
            self.assertEqual(report["result"], "FAIL")
            self.assertIn("three coordinates", str(report["rejected"][stage.name]))
            refiner = subprocess.run([sys.executable, "-B", "-m", "cover_verifier.refine",
                                      str(cert), str(receipt), str(cert)], cwd=cover, capture_output=True)
            self.assertNotEqual(refiner.returncode, 0)
            self.assertIn(b"aliases an input", refiner.stderr)
            self.assertEqual(stage.read_bytes(), original)

    def test_protects_all_inputs_before_first_write(self):
        with tempfile.TemporaryDirectory() as tmp:
            cert = Path(tmp) / "certificate"
            cert.mkdir()
            first, second = cert / "stage01.jsonl", cert / "stage02.jsonl"
            first.write_bytes(b"first\n")
            second.write_bytes(b"second\n")
            receipt = Path(tmp) / "receipt.json"
            receipt.write_text('{"rejected":{}}', encoding="utf-8")
            before = [p.read_bytes() for p in (first, second, receipt)]
            with self.assertRaises(SystemExit), redirect_stderr(io.StringIO()):
                refine.main([str(cert), str(receipt), str(cert / ".." / cert.name)])
            for source in (first, second, receipt):
                output = Path(tmp) / source.name
                if output == receipt:
                    output = Path(tmp) / "receipt-alias"
                output.mkdir()
                os.link(source, output / second.name)
                with self.subTest(source=source.name), self.assertRaises(SystemExit), redirect_stderr(io.StringIO()):
                    refine.main([str(cert), str(receipt), str(output)])
                self.assertFalse((output / first.name).exists())
                self.assertEqual([p.read_bytes() for p in (first, second, receipt)], before)
            separate = Path(tmp) / "separate"
            with redirect_stdout(io.StringIO()):
                self.assertEqual(refine.main([str(cert), str(receipt), str(separate)]), 0)
            self.assertEqual([(separate / p.name).read_bytes() for p in (first, second)], before[:2])
