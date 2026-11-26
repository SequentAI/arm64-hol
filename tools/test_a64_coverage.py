import unittest
from pathlib import Path

from a64_coverage import ARCHITECTURAL_TOTAL, INVENTORY, _code_has_form, _coverage_with_marker, _encoding_matches, _probe_words, coverage


ROOT = Path(__file__).resolve().parents[1]
HAS_CONTRACT_FIXTURES = any((ROOT / "examples").glob("*/*CodeScript.sml"))


class A64CoverageTests(unittest.TestCase):
    def test_inventory_is_fixed_and_fixture_independent(self):
        report = coverage(ROOT)
        self.assertEqual(len(INVENTORY), ARCHITECTURAL_TOTAL)
        self.assertEqual(report["summary"]["architectural_total"], ARCHITECTURAL_TOTAL)
        self.assertTrue(all(form.mask and all(_encoding_matches(form, word) for word in _probe_words(form))
                            for form in INVENTORY))
        self.assertGreater(report["summary"]["unimplemented"], 0)
        self.assertTrue(all("native" in row["evidence"] for row in report["rows"]))
        self.assertTrue(all(
            row["evidence"]["hol_decode_probe"]
            for row in report["rows"]
            if row["architectural_status"] != "valid_but_unimplemented"
        ))
        self.assertTrue(all(
            row["evidence"]["hol_decode_negative_probe"]
            for row in report["rows"]
            if row["architectural_status"] == "valid_but_unimplemented"
        ))
        self.assertEqual(
            next(row for row in report["rows"] if row["form_id"] == "dp-imm.addsub-immediate.w")["evidence"]["execution_evidence_level"],
            "theorem",
        )
        self.assertEqual(
            next(row for row in report["rows"] if row["form_id"] == "dp-imm.move-wide-zero.w")["evidence"]["execution_evidence_level"],
            "definition",
        )
        shift = next(form for form in INVENTORY if form.form_id == "simd.shift")
        self.assertFalse(_encoding_matches(shift, 0x4F105400))
        logical_and = next(form for form in INVENTORY if form.form_id == "dp-imm.logical-mask-and")
        self.assertTrue(_encoding_matches(logical_and, 0x12000800))
        byte_mask = next(form for form in INVENTORY if form.form_id == "dp-imm.and-byte-mask")
        self.assertFalse(_code_has_form("0x12001c42w", logical_and))
        self.assertTrue(_code_has_form("0x12001c42w", byte_mask))
        literal = next(form for form in INVENTORY if form.form_id == "load-store.literal")
        self.assertTrue(_encoding_matches(literal, 0x9C000000))
        self.assertFalse(_encoding_matches(literal, 0xD8000000))
        self.assertTrue(_encoding_matches(next(form for form in INVENTORY if form.form_id == "simd.shift"), 0x4F4057DF))
        self.assertTrue(all(
            any(_encoding_matches(form, word) for form in INVENTORY)
            for word in (0x72000000, 0x5AC01400, 0xDAC01400, 0xD50320BF,
                         0x5AC00400, 0xDAC00400, 0xD4200000, 0x6E228420,
                         0x4E228420, 0x4E628420)
        ))
        unscaled = next(form for form in INVENTORY if form.form_id == "load-store.single-immediate-unscaled")
        pair = next(form for form in INVENTORY if form.form_id == "load-store.pair")
        self.assertFalse(_encoding_matches(unscaled, 0x38000820))
        self.assertFalse(_encoding_matches(pair, 0xA8000440))
        nontemporal = next(form for form in INVENTORY if form.form_id == "load-store.pair-nontemporal")
        self.assertFalse(_encoding_matches(nontemporal, 0xA9017C1F))
        ands = next(form for form in INVENTORY if form.form_id == "dp-imm.logical-immediate-ands")
        self.assertFalse(_encoding_matches(ands, 0x72001C1F))
        shifted_w = next(form for form in INVENTORY if form.form_id == "dp-reg.addsub-shifted.w")
        shifted_x = next(form for form in INVENTORY if form.form_id == "dp-reg.addsub-shifted.x")
        extended_w = next(form for form in INVENTORY if form.form_id == "dp-reg.addsub-extended.w")
        extended_x = next(form for form in INVENTORY if form.form_id == "dp-reg.addsub-extended.x")
        self.assertFalse(_encoding_matches(shifted_w, 0x0BC00000))
        self.assertFalse(_encoding_matches(shifted_x, 0x8BC00000))
        self.assertFalse(_encoding_matches(shifted_w, 0x0B008000))
        self.assertFalse(_encoding_matches(extended_w, 0x0B201400))
        self.assertFalse(_encoding_matches(extended_x, 0x8B201400))
        move_wide = next(row for row in report["rows"] if row["form_id"] == "dp-imm.move-wide-zero.w")
        self.assertFalse(move_wide["evidence"]["universal_sources"])
        self.assertIn("arm64IsaTheory.encode_of_decode", move_wide["evidence"]["definition_sources"])
        literal_row = next(row for row in report["rows"] if row["form_id"] == "load-store.literal")
        self.assertEqual(len(literal_row["encoding_partitions"]), 6)
        clz = next(row for row in report["rows"] if row["form_id"] == "dp-reg.clz.w")
        self.assertTrue(clz["evidence"]["l3_discrepancy"])
        crc = next(form for form in INVENTORY if form.form_id == "crypto.crc32")
        self.assertFalse(_encoding_matches(crc, 0x1AC15C00))
        self.assertTrue(_encoding_matches(crc, 0x9AC05C00))

    @unittest.skipUnless(HAS_CONTRACT_FIXTURES, "generated C scripts are optional")
    def test_contract_evidence_is_separate_when_fixtures_are_present(self):
        report = coverage(ROOT)
        move_wide = next(row for row in report["rows"] if row["form_id"] == "dp-imm.move-wide-zero.w")
        self.assertTrue(move_wide["evidence"]["universal_contract_sources"])
        self.assertFalse(move_wide["evidence"]["universal_sources"])

    def test_add_acceptance_keeps_denominator_and_flags_exact_row(self):
        baseline = coverage(ROOT)
        add_rows = [row for row in baseline["rows"] if row["constructor"] in {"AddImm", "AddShift", "AddExtend", "AddCarry"}]
        self.assertEqual(len(add_rows), 8)
        self.assertTrue(all(row["status"] == "implemented" for row in add_rows))
        hidden = "dp-imm.addsub-immediate.w"
        regression = _coverage_with_marker(ROOT, hidden)
        self.assertEqual(
            regression["summary"]["architectural_total"],
            baseline["summary"]["architectural_total"],
        )
        row = next(item for item in regression["rows"] if item["form_id"] == hidden)
        self.assertNotEqual(row["status"], "implemented")
        baseline_missing = {
            item["form_id"] for item in baseline["rows"] if item["status"] != "implemented"
        }
        missing = {
            item["form_id"] for item in regression["rows"] if item["status"] != "implemented"
        }
        self.assertEqual(missing, baseline_missing | {hidden})

    def test_valid_unimplemented_forms_are_reported(self):
        report = coverage(ROOT)
        missing = {
            row["form_id"] for row in report["rows"]
            if row["architectural_status"] == "valid_but_unimplemented"
        }
        reported = {
            row["form_id"] for row in report["rows"]
            if row["status"] != "implemented" and not row["evidence"]["decode"]
        }
        self.assertTrue(missing)
        self.assertTrue(missing <= reported)

    def test_grouped_rows_probe_every_advertised_variant(self):
        expected_probe_counts = {
            "branch.unconditional": 2,
            "branch.conditional": 16,
            "branch.compare": 4,
            "branch.test": 4,
            "dp-imm.pc-relative": 2,
            "dp-reg.logical-shifted": 8,
            "dp-reg.conditional-select": 8,
            "dp-reg.multiply-add": 4,
            "dp-reg.divide": 4,
        }
        for form_id, count in expected_probe_counts.items():
            form = next(form for form in INVENTORY if form.form_id == form_id)
            self.assertEqual(len(_probe_words(form)), count, form_id)

    def test_unimplemented_architectural_samples_have_one_partition(self):
        samples = (
            0xF8200020, 0xC8A07C00, 0xACC00440, 0xADC00440, 0xAC800440,
            0x3CE06800, 0x3C800400, 0x6EA08420, 0x4EA09C20, 0x5E020800,
            0x4E20D400, 0xD53BD040, 0x0E000000, 0x4E002000,
        )
        for word in samples:
            matches = [form.form_id for form in INVENTORY if _encoding_matches(form, word)]
            self.assertEqual(len(matches), 1, hex(word))


if __name__ == "__main__":
    unittest.main()
