#!/usr/bin/env python3
"""Tests for harness.py's comparison, vault and path logic.

WHY ONLY THIS PART. The comparison is the piece of the harness most likely to
be quietly wrong: it returns a plausible-looking verdict whatever it does, and
a diff that reports agreement it never measured is worse than no diff at all.
Several instruments in this repository returned credible numbers while
measuring nothing, and none was caught by reading them.

So every test below is written so that the OLD, WRONG behaviour would fail it.
Each one names the mistake it guards against. All of it is pure computation on
synthetic inputs: no family is run, nothing is simulated.

    python3 -m unittest discover -s <this directory> -p 'test_harness_*.py'
    python3 test_harness_diff.py
"""

import json
import math
import os
import shutil
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import harness  # noqa: E402


class TestKind(unittest.TestCase):
    """`True == 1` in Python, and that must never let a verdict flip hide."""

    def test_bool_is_not_a_number(self):
        self.assertEqual(harness.kind_of(True), "bool")
        self.assertEqual(harness.kind_of(1), "number")
        self.assertEqual(harness.kind_of(1.0), "number")

    def test_kinds(self):
        self.assertEqual(harness.kind_of(None), "null")
        self.assertEqual(harness.kind_of("x"), "string")
        self.assertEqual(harness.kind_of([]), "list")
        self.assertEqual(harness.kind_of({}), "dict")


class TestPaths(unittest.TestCase):

    def test_render(self):
        self.assertEqual(harness.render_path([]), "$")
        self.assertEqual(harness.render_path(["a", 0, "b"]), "$.a[0].b")

    def test_ignore_covers_descendants(self):
        pats = ["$._provenance"]
        self.assertTrue(harness.path_ignored("$._provenance", pats))
        self.assertTrue(harness.path_ignored("$._provenance.revision", pats))
        self.assertTrue(harness.path_ignored("$._provenance.argv[0]", pats))

    def test_ignore_does_not_leak_to_siblings(self):
        # `$.run` must not swallow `$.runtime_sec`: a prefix match without the
        # separator would silently drop a neighbouring key.
        pats = ["$.run"]
        self.assertFalse(harness.path_ignored("$.runtime_sec", pats))
        self.assertTrue(harness.path_ignored("$.run.x", pats))

    def test_ignore_globs(self):
        # `[*]` must mean ANY INDEX. Read as an fnmatch character class it
        # matches only a literal `[*]`, i.e. nothing -- a pattern that silently
        # matches nothing is the `sed` failure in another costume.
        self.assertTrue(harness.path_ignored("$.C1.cells[3].se",
                                             ["$.C1.cells[*].se"]))
        self.assertTrue(harness.path_ignored("$.C1.cells[117].se",
                                             ["$.C1.cells[*].se"]))

    def test_index_glob_does_not_match_a_different_key(self):
        self.assertFalse(harness.path_ignored("$.C1.cells[3].mean",
                                              ["$.C1.cells[*].se"]))
        self.assertFalse(harness.path_ignored("$.C2.cells[3].se",
                                              ["$.C1.cells[*].se"]))

    def test_star_glob_still_works(self):
        self.assertTrue(harness.path_ignored("$.timing_ms", ["$.timing*"]))

    def test_the_matching_pattern_is_returned_not_just_true(self):
        # So the summary can say WHICH rule dropped a path. An exclusion nobody
        # can trace is how a real difference disappears.
        self.assertEqual(
            harness.path_ignored("$._provenance.revision", ["$.x", "$._provenance"]),
            "$._provenance")


class TestNumericDiff(unittest.TestCase):

    def test_identical(self):
        d = harness.compare_json({"a": 1.0}, {"a": 1.0}, ignore=[])
        self.assertTrue(d["identical"])
        self.assertEqual(harness.diff_verdict(d), "IDENTICAL")
        self.assertEqual(d["leaves_compared"], 1)

    def test_reduction_order_is_not_disagreement(self):
        # The real case: two confirmed families at worst relative differences
        # of 1.8e-14 and 3.3e-13.
        stored = {"p": 0.37421, "q": 1234.5}
        fresh = {"p": 0.37421 * (1 + 1.8e-14), "q": 1234.5 * (1 + 3.3e-13)}
        d = harness.compare_json(stored, fresh, ignore=[], rtol=1e-9)
        self.assertEqual(harness.diff_verdict(d), "AGREES_TO_FLOATING_POINT")
        self.assertEqual(d["structural_count"], 0)
        self.assertEqual(d["numeric_differing_count"], 2)
        self.assertEqual(d["numeric_beyond_tolerance_count"], 0)
        self.assertTrue(d["agrees_within_tolerance"])
        self.assertLess(d["numeric_worst_rel"]["rel"], 1e-12)

    def test_real_disagreement_is_reported(self):
        d = harness.compare_json({"p": 1.0}, {"p": 1.9}, ignore=[], rtol=1e-9)
        self.assertEqual(harness.diff_verdict(d), "NUMERIC_DIFFERENCE")
        self.assertEqual(d["numeric_beyond_tolerance_count"], 1)
        self.assertAlmostEqual(d["numeric_worst_abs"]["abs"], 0.9)
        self.assertAlmostEqual(d["numeric_worst_rel"]["rel"], 0.9 / 1.9)

    def test_worst_abs_and_worst_rel_can_be_different_leaves(self):
        # A big absolute move on a big number and a small absolute move on a
        # tiny one: reporting only one of the two hides half the story.
        stored = {"big": 1e6, "tiny": 1e-9}
        fresh = {"big": 1e6 + 10.0, "tiny": 2e-9}
        d = harness.compare_json(stored, fresh, ignore=[], rtol=1e-12)
        self.assertEqual(d["numeric_worst_abs"]["path"], "$.big")
        self.assertEqual(d["numeric_worst_rel"]["path"], "$.tiny")

    def test_relative_against_zero(self):
        # Denominator zero on one side: max(|a|,|b|) is the scale, so this is a
        # relative difference of exactly 1 rather than a ZeroDivisionError or a
        # silently dropped leaf.
        d = harness.compare_json({"x": 0.0}, {"x": 1e-30}, ignore=[])
        self.assertEqual(d["numeric_differing_count"], 1)
        self.assertEqual(d["numeric_worst_rel"]["rel"], 1.0)
        self.assertEqual(harness.diff_verdict(d), "NUMERIC_DIFFERENCE")

    def test_both_zero_is_equal(self):
        d = harness.compare_json({"x": 0.0}, {"x": 0}, ignore=[])
        self.assertTrue(d["identical"])

    def test_atol_admits_a_small_absolute_move(self):
        d = harness.compare_json({"x": 0.0}, {"x": 1e-14}, ignore=[],
                                 rtol=0.0, atol=1e-12)
        self.assertEqual(harness.diff_verdict(d), "AGREES_TO_FLOATING_POINT")


class TestNonFinite(unittest.TestCase):
    """NaN and infinity have no relative difference. They are structural, and
    they are never dropped: a cell whose replicates started failing is exactly
    what a NaN appearing means."""

    def test_nan_to_nan_is_equal(self):
        nan = float("nan")
        d = harness.compare_json({"x": nan}, {"x": nan}, ignore=[])
        self.assertTrue(d["identical"])

    def test_nan_appearing_is_structural(self):
        d = harness.compare_json({"x": 1.0}, {"x": float("nan")}, ignore=[])
        self.assertEqual(d["structural_count"], 1)
        self.assertEqual(d["structural"][0]["reason"], "nan mismatch")
        self.assertEqual(harness.diff_verdict(d), "STRUCTURAL_DIFFERENCE")

    def test_nan_resolving_is_structural(self):
        d = harness.compare_json({"x": float("nan")}, {"x": 1.0}, ignore=[])
        self.assertEqual(d["structural_count"], 1)

    def test_matching_infinities_are_equal(self):
        inf = float("inf")
        d = harness.compare_json({"x": inf}, {"x": inf}, ignore=[])
        self.assertTrue(d["identical"])

    def test_sign_flipped_infinity_is_structural(self):
        d = harness.compare_json({"x": float("inf")}, {"x": float("-inf")},
                                 ignore=[])
        self.assertEqual(d["structural_count"], 1)
        self.assertEqual(d["structural"][0]["reason"], "infinity mismatch")

    def test_infinity_against_finite_is_structural(self):
        d = harness.compare_json({"x": 1e300}, {"x": float("inf")}, ignore=[])
        self.assertEqual(d["structural_count"], 1)
        self.assertEqual(d["numeric_differing_count"], 0)


class TestStructuralDiff(unittest.TestCase):

    def test_key_missing_from_fresh(self):
        d = harness.compare_json({"a": 1, "b": 2}, {"a": 1}, ignore=[])
        self.assertEqual(d["structural_count"], 1)
        self.assertEqual(d["structural"][0]["reason"], "key missing from fresh")
        self.assertEqual(d["structural"][0]["path"], "$.b")

    def test_key_added_in_fresh(self):
        d = harness.compare_json({"a": 1}, {"a": 1, "b": 2}, ignore=[])
        self.assertEqual(d["structural"][0]["reason"], "key added in fresh")

    def test_list_length_change(self):
        d = harness.compare_json({"c": [1, 2, 3]}, {"c": [1, 2]}, ignore=[])
        self.assertEqual(d["structural_count"], 1)
        self.assertEqual(d["structural"][0]["reason"], "list length changed")
        self.assertEqual(d["structural"][0]["stored_len"], 3)
        self.assertEqual(d["structural"][0]["fresh_len"], 2)

    def test_length_change_does_not_hide_element_moves(self):
        # A length change and a value change at once. Reporting only the length
        # would let a real numeric disagreement in the surviving elements go
        # unmeasured.
        d = harness.compare_json({"c": [1.0, 2.0, 3.0]}, {"c": [1.0, 9.0]},
                                 ignore=[])
        self.assertEqual(d["structural_count"], 1)
        self.assertEqual(d["numeric_beyond_tolerance_count"], 1)
        self.assertEqual(d["numeric_worst_abs"]["path"], "$.c[1]")

    def test_type_change(self):
        d = harness.compare_json({"a": 1.0}, {"a": "1.0"}, ignore=[])
        self.assertEqual(d["structural"][0]["reason"], "type changed")
        self.assertEqual(d["structural"][0]["stored_kind"], "number")
        self.assertEqual(d["structural"][0]["fresh_kind"], "string")

    def test_null_appearing_is_a_type_change(self):
        d = harness.compare_json({"se": 0.01}, {"se": None}, ignore=[])
        self.assertEqual(d["structural_count"], 1)
        self.assertEqual(d["numeric_differing_count"], 0)

    def test_verdict_flip_is_structural_not_numeric(self):
        # THE ONE THAT MATTERS. With bools treated as numbers, READ_THE_TEST
        # going true -> false is a numeric difference of 1.0 sitting among the
        # floats, and the family changing its verdict goes unread.
        d = harness.compare_json(
            {"READ_THE_TEST": True, "failed_checks": []},
            {"READ_THE_TEST": False, "failed_checks": ["C3 sealing law"]},
            ignore=[])
        self.assertEqual(harness.diff_verdict(d), "STRUCTURAL_DIFFERENCE")
        reasons = sorted(s["reason"] for s in d["structural"])
        self.assertIn("boolean flipped", reasons)
        self.assertIn("list length changed", reasons)
        self.assertEqual(d["numeric_differing_count"], 0)

    def test_bool_against_number_is_a_type_change(self):
        d = harness.compare_json({"ok": True}, {"ok": 1}, ignore=[])
        self.assertEqual(d["structural"][0]["reason"], "type changed")

    def test_string_change(self):
        d = harness.compare_json({"note": "a"}, {"note": "b"}, ignore=[])
        self.assertEqual(d["structural"][0]["reason"], "string changed")

    def test_structural_dominates_numeric_in_the_verdict(self):
        d = harness.compare_json({"a": 1.0, "b": 1}, {"a": 2.0}, ignore=[])
        self.assertEqual(harness.diff_verdict(d), "STRUCTURAL_DIFFERENCE")
        self.assertEqual(d["numeric_beyond_tolerance_count"], 1)


class TestIgnores(unittest.TestCase):

    def test_provenance_is_ignored_by_default(self):
        stored = {"_provenance": {"revision": "aaa", "runAt": "t1"}, "x": 1.0}
        fresh = {"_provenance": {"revision": "bbb", "runAt": "t2"}, "x": 1.0}
        d = harness.compare_json(stored, fresh)
        self.assertTrue(d["identical"])
        self.assertEqual(d["ignored_count"], 1)

    def test_ignored_paths_are_recorded_not_vanished(self):
        d = harness.compare_json({"runtime_sec": 1.0}, {"runtime_sec": 900.0})
        self.assertTrue(d["identical"])
        self.assertEqual([i["path"] for i in d["ignored_paths"]],
                         ["$.runtime_sec"])

    def test_ignoring_provenance_does_not_ignore_the_science(self):
        stored = {"_provenance": {"revision": "aaa"}, "C1": {"ratio": 1.0}}
        fresh = {"_provenance": {"revision": "bbb"}, "C1": {"ratio": 1.9}}
        d = harness.compare_json(stored, fresh)
        self.assertEqual(harness.diff_verdict(d), "NUMERIC_DIFFERENCE")


class TestNesting(unittest.TestCase):

    def test_deep_paths_are_reported_exactly(self):
        stored = {"C4": {"cells": [{"fit": {"coef": [1.0, 2.0]}}]}}
        fresh = {"C4": {"cells": [{"fit": {"coef": [1.0, 2.5]}}]}}
        d = harness.compare_json(stored, fresh, ignore=[])
        self.assertEqual(d["numeric_worst_abs"]["path"],
                         "$.C4.cells[0].fit.coef[1]")

    def test_leaves_counted_across_nesting(self):
        doc = {"a": [1.0, 2.0], "b": {"c": "s", "d": None, "e": True}}
        d = harness.compare_json(doc, json.loads(json.dumps(doc)), ignore=[])
        self.assertEqual(d["leaves_compared"], 5)
        self.assertEqual(d["leaves_equal"], 5)

    def test_empty_documents(self):
        d = harness.compare_json({}, {}, ignore=[])
        self.assertTrue(d["identical"])
        self.assertEqual(d["leaves_compared"], 0)

    def test_top_level_list_documents(self):
        d = harness.compare_json([1.0, 2.0], [1.0, 3.0], ignore=[])
        self.assertEqual(d["numeric_worst_abs"]["path"], "$[1]")


class TestTruncation(unittest.TestCase):
    """The true count is always reported, even when the examples are capped:
    a summary that says 'and more' without a number is unreadable."""

    def test_counts_survive_the_cap(self):
        stored = dict(("k%03d" % i, float(i)) for i in range(200))
        fresh = dict(("k%03d" % i, float(i) + 1.0) for i in range(200))
        d = harness.compare_json(stored, fresh, ignore=[], max_examples=5)
        self.assertEqual(d["numeric_differing_count"], 200)
        self.assertEqual(d["numeric_beyond_tolerance_count"], 200)
        self.assertEqual(len(d["numeric_beyond_tolerance"]), 5)
        self.assertEqual(d["numeric_beyond_truncated"], 195)

    def test_structural_counts_survive_the_cap(self):
        stored = dict(("k%03d" % i, 1) for i in range(30))
        d = harness.compare_json(stored, {}, ignore=[], max_examples=4)
        self.assertEqual(d["structural_count"], 30)
        self.assertEqual(len(d["structural"]), 4)
        self.assertEqual(d["structural_truncated"], 26)


class TestHeadline(unittest.TestCase):
    """The verdict line is the only thing many readers will see."""

    def test_headline_never_raises_on_any_verdict(self):
        cases = [
            ({"a": 1.0}, {"a": 1.0}),
            ({"a": 1.0}, {"a": 1.0 + 1e-15}),
            ({"a": 1.0}, {"a": 2.0}),
            ({"a": 1.0}, {"b": 2.0}),
            ({}, {}),
        ]
        for stored, fresh in cases:
            d = harness.compare_json(stored, fresh, ignore=[])
            line = harness.diff_headline(d)
            self.assertTrue(line and isinstance(line, str))
            self.assertIn(harness.diff_verdict(d), harness.VERDICT_ORDER)

    def test_alarming_set_matches_the_ordering_table(self):
        for v in harness.ALARMING:
            self.assertIn(v, harness.VERDICT_ORDER)
        # The two benign comparison outcomes must not be alarming, or every
        # confirmed family reads as a finding and the list stops being read.
        self.assertNotIn("IDENTICAL", harness.ALARMING)
        self.assertNotIn("AGREES_TO_FLOATING_POINT", harness.ALARMING)


class TestVaultAndCopy(unittest.TestCase):
    """Rule 4: after a transformation, prove something happened."""

    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="harness-test-")

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def _write(self, name, text):
        p = os.path.join(self.tmp, name)
        fh = open(p, "w")
        fh.write(text)
        fh.close()
        return p

    def test_stash_and_restore_round_trip(self):
        p = self._write("stored.json", '{"x": 1}')
        vault = harness.Vault(os.path.join(self.tmp, "_vault"))
        digest = vault.stash(p)
        # The family clobbers it, as several families in this directory do.
        fh = open(p, "w")
        fh.write('{"x": 999}')
        fh.close()
        self.assertNotEqual(harness.sha256_file(p), digest)
        vault.restore(digest, p)
        self.assertEqual(harness.sha256_file(p), digest)
        fh = open(p)
        try:
            self.assertEqual(fh.read(), '{"x": 1}')
        finally:
            fh.close()

    def test_restore_of_an_unknown_digest_fails_loudly(self):
        vault = harness.Vault(os.path.join(self.tmp, "_vault"))
        p = self._write("a.json", "{}")
        self.assertRaises(harness.HarnessError, vault.restore, "0" * 64, p)

    def test_vault_is_content_addressed(self):
        a = self._write("a.json", "same")
        b = self._write("b.json", "same")
        vault = harness.Vault(os.path.join(self.tmp, "_vault"))
        self.assertEqual(vault.stash(a), vault.stash(b))
        self.assertEqual(len(os.listdir(os.path.join(self.tmp, "_vault"))), 1)

    def test_copy_verified_returns_the_hash_of_what_arrived(self):
        src = self._write("src.json", '{"n": 3}')
        dst = os.path.join(self.tmp, "dst.json")
        got = harness.copy_verified(src, dst)
        self.assertEqual(got, harness.sha256_file(dst))
        fh = open(dst)
        try:
            self.assertEqual(fh.read(), '{"n": 3}')
        finally:
            fh.close()

    def test_snapshot_covers_every_json_beside_the_family(self):
        self._write("fam_a_results.json", "{}")
        self._write("fam_b_results.json", "[]")
        self._write("notes.txt", "ignored")
        vault = harness.Vault(os.path.join(self.tmp, "_vault"))
        snap = harness.snapshot_dir_json(self.tmp, vault)
        self.assertEqual(sorted(snap), ["fam_a_results.json",
                                        "fam_b_results.json"])

    def test_file_stat_identifies_the_same_file(self):
        p = self._write("x.json", "{}")
        a, b = harness.file_stat(p), harness.file_stat(p)
        self.assertEqual((a["dev"], a["ino"]), (b["dev"], b["ino"]))
        self.assertIsNone(harness.file_stat(os.path.join(self.tmp, "nope")))


class TestRepoRoot(unittest.TestCase):
    """Never located by counting parent directories."""

    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="harness-root-")

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def test_walks_up_to_dot_git(self):
        root = os.path.join(self.tmp, "repo")
        deep = os.path.join(root, "a", "b", "c")
        os.makedirs(deep)
        os.makedirs(os.path.join(root, ".git"))
        self.assertEqual(harness.find_repo_root(deep), root)

    def test_depth_does_not_change_the_answer(self):
        # The whole point: moving the caller one level deeper must not move the
        # answer, which is exactly what parents[2] failed to guarantee.
        root = os.path.join(self.tmp, "repo")
        os.makedirs(os.path.join(root, ".git"))
        shallow = os.path.join(root, "a")
        deeper = os.path.join(root, "a", "b", "c", "d")
        os.makedirs(deeper)
        self.assertEqual(harness.find_repo_root(shallow),
                         harness.find_repo_root(deeper))

    def test_no_git_returns_none_rather_than_a_plausible_wrong_path(self):
        deep = os.path.join(self.tmp, "x", "y")
        os.makedirs(deep)
        self.assertIsNone(harness.find_repo_root(deep))


class TestManifest(unittest.TestCase):

    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="harness-man-")

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def test_parses_arguments_and_skips_comments(self):
        p = os.path.join(self.tmp, "m.txt")
        fh = open(p, "w")
        fh.write("# comment\n\nfam_a.py --profile full\n"
                 "fam_b.py --set 'x = 1'\n")
        fh.close()
        jobs = harness.read_manifest(p)
        self.assertEqual(jobs, [("fam_a.py", ["--profile", "full"]),
                                ("fam_b.py", ["--set", "x = 1"])])

    def test_an_empty_manifest_is_an_error_not_a_silent_no_op(self):
        p = os.path.join(self.tmp, "m.txt")
        fh = open(p, "w")
        fh.write("# nothing here\n")
        fh.close()
        self.assertRaises(SystemExit, harness.read_manifest, p)


class TestOutputFlagDetection(unittest.TestCase):
    """Detected by reading the source, never by running the family.

    The first version asked with `<script> --help`. A family with no argparse
    does not print help in response to that: it RUNS. On the real families here
    that is a second full simulation, silently, just to answer a question about
    a flag.
    """

    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="harness-flag-")

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def _script(self, body):
        p = os.path.join(self.tmp, "fam_x.py")
        fh = open(p, "w")
        fh.write(body)
        fh.close()
        return p

    def test_detects_a_registered_output_flag(self):
        ok, _ = self._detect('parser.add_argument("--output", default="a.json")')
        self.assertTrue(ok)

    def test_detects_single_quoted_and_spaced_registrations(self):
        self.assertTrue(self._detect("p.add_argument(  '--output')")[0])

    def test_a_family_with_no_argparse_is_not_given_the_flag(self):
        ok, why = self._detect('import json\nprint("no flags here")\n')
        self.assertFalse(ok)
        self.assertIn("working directory", why)

    def test_a_docstring_mention_is_not_a_registration(self):
        # A bare substring search for '--output' would pass the flag to a
        # family that only mentions it in prose, and the run would die in
        # argparse having measured nothing.
        ok, _ = self._detect('"""Writes to --output, someday."""\n')
        self.assertFalse(ok)

    def test_the_reason_is_always_stated(self):
        for body in ('parser.add_argument("--output")', "x = 1\n"):
            ok, why = self._detect(body)
            self.assertTrue(why)

    def test_an_unreadable_script_says_so_rather_than_guessing(self):
        ok, why = harness.supports_output_flag(
            os.path.join(self.tmp, "does_not_exist.py"))
        self.assertFalse(ok)
        self.assertIn("could not read", why)

    def _detect(self, body):
        return harness.supports_output_flag(self._script(body))


class TestRealFamiliesAreClassifiedCorrectly(unittest.TestCase):
    """The detection is checked against the families actually in this
    directory, since a rotting hardcoded list is what it replaces."""

    def test_known_families(self):
        here = os.path.dirname(os.path.abspath(__file__))
        expected = {
            "fam_permeability.py": True,
            "fam_im_coalescent.py": True,
            "fam_metrics.py": False,     # writes to os.path.join(HERE, ...)
            "fam_selection.py": False,
            "fam_freezing.py": False,
        }
        for name, want in sorted(expected.items()):
            path = os.path.join(here, name)
            if not os.path.isfile(path):
                continue  # a family may legitimately have been renamed
            got, why = harness.supports_output_flag(path)
            self.assertEqual(got, want, "%s: %s" % (name, why))


class TestInterpreterVerification(unittest.TestCase):
    """Rule 6. The one thing here that runs a subprocess, and it runs only the
    interpreter already running this test."""

    def test_the_current_interpreter_verifies(self):
        info = harness.verify_interpreter(sys.executable, (3, 0), [])
        self.assertTrue(info["usable"], info.get("problem"))
        self.assertEqual(info["version"], sys.version.split()[0])

    def test_a_missing_interpreter_is_a_refusal_with_a_reason(self):
        info = harness.verify_interpreter("/nonexistent/python9.9", (3, 6), [])
        self.assertFalse(info["usable"])
        self.assertIn("not found", info["problem"])

    def test_too_old_is_refused(self):
        # Stand-in for the cluster's 3.6.8 against a modern requirement: the
        # failure must be named here, not discovered as a SyntaxError later
        # whose nonzero exit is indistinguishable from a finding.
        info = harness.verify_interpreter(sys.executable, (99, 0), [])
        self.assertFalse(info["usable"])
        self.assertIn("below the required", info["problem"])

    def test_a_missing_required_import_is_refused(self):
        info = harness.verify_interpreter(
            sys.executable, (3, 0), ["definitely_not_a_real_module_xyzzy"])
        self.assertFalse(info["usable"])
        self.assertIn("cannot import", info["problem"])


class TestSummaryText(unittest.TestCase):
    """The verdict goes at the top, and a nonzero family exit is not alarming
    by itself."""

    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="harness-sum-")
        self.opts = {"rtol": 1e-9, "atol": 0.0,
                     "interpreter_info": {"version": "3.12.0",
                                          "resolved": "/usr/bin/python3.12"}}
        self.stamp = {"revision": "a" * 40, "workingTreeClean": True,
                      "workingTreeDirtyPaths": [], "runAt": "2026-08-03T00:00:00Z",
                      "host": "node1", "python": "3.12.0"}

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def _summary(self, stem, verdict, code):
        return {"family": {"stem": stem}, "verdict": verdict,
                "verdict_detail": "detail for " + stem,
                "exit": {"code": code}, "notes": []}

    def test_verdict_block_precedes_detail(self):
        path = os.path.join(self.tmp, "SUMMARY.txt")
        text = harness.write_summary_text(
            path, self.stamp,
            [self._summary("fam_a", "IDENTICAL", 0),
             self._summary("fam_b", "STRUCTURAL_DIFFERENCE", 1)],
            self.opts)
        self.assertLess(text.index("VERDICT"), text.index("DETAIL"))
        self.assertLess(text.index("STRUCTURAL_DIFFERENCE"),
                        text.index("PROVENANCE"))
        fh = open(path)
        try:
            self.assertEqual(fh.read(), text)
        finally:
            fh.close()

    def test_alarming_families_are_listed_first(self):
        text = harness.write_summary_text(
            os.path.join(self.tmp, "S.txt"), self.stamp,
            [self._summary("fam_ok", "IDENTICAL", 0),
             self._summary("fam_bad", "NO_RESULTS", 0)],
            self.opts)
        self.assertLess(text.index("fam_bad"), text.index("fam_ok"))

    def test_a_nonzero_family_exit_is_not_alarming_by_itself(self):
        # The probe-harness failure, inverted into a test: a family that failed
        # a check on stdout and exited 1 while agreeing with its stored result
        # must read as agreeing.
        text = harness.write_summary_text(
            os.path.join(self.tmp, "S.txt"), self.stamp,
            [self._summary("fam_x", "AGREES_TO_FLOATING_POINT", 1)],
            self.opts)
        self.assertIn("none needs reading", text)
        self.assertIn("exit 1", text)

    def test_an_empty_run_still_writes_a_readable_verdict(self):
        text = harness.write_summary_text(
            os.path.join(self.tmp, "S.txt"), self.stamp, [], self.opts)
        self.assertIn("no families have completed yet", text)

    def test_a_dirty_tree_is_stated_in_the_provenance_block(self):
        stamp = dict(self.stamp)
        stamp["workingTreeClean"] = False
        stamp["workingTreeDirtyPaths"] = ["M x.lean", "M y.lean"]
        text = harness.write_summary_text(
            os.path.join(self.tmp, "S.txt"), stamp, [], self.opts)
        self.assertIn("TREE DIRTY (2 paths)", text)


class TestRealisticFamilyShape(unittest.TestCase):
    """Against the schema the families here actually emit."""

    def _doc(self, rev, ratio, ok):
        return {
            "_provenance": {"revision": rev, "runAt": "2026-08-03T01:02:03Z",
                            "host": "n1", "python": "3.12.0", "config": {}},
            "profile": "full", "seed": 20260803, "overrides": {},
            "config": {"C1_R_ENS": 400},
            "C1": {"measured_over_predicted": ratio,
                   "cells": [{"m": 1000, "rmse": 0.031, "se": 0.0004}]},
            "C2": {"pass": True},
            "READ_THE_TEST": ok, "failed_checks": [] if ok else ["C1"],
            "runtime_sec": 812.4,
        }

    def test_a_rerun_at_another_revision_agrees(self):
        d = harness.compare_json(self._doc("aaa", 1.0000000, True),
                                 self._doc("bbb", 1.0000000 + 3.3e-13, True))
        self.assertEqual(harness.diff_verdict(d), "AGREES_TO_FLOATING_POINT")
        self.assertIn("reduction order", harness.diff_headline(d))

    def test_a_flipped_verdict_leads_the_report(self):
        d = harness.compare_json(self._doc("aaa", 1.0, True),
                                 self._doc("bbb", 1.9, False))
        self.assertEqual(harness.diff_verdict(d), "STRUCTURAL_DIFFERENCE")
        paths = [s["path"] for s in d["structural"]]
        self.assertIn("$.READ_THE_TEST", paths)
        self.assertIn("$.failed_checks", paths)
        # And the numeric finding underneath it is still measured, not lost.
        self.assertEqual(d["numeric_beyond_tolerance_count"], 1)
        self.assertEqual(d["numeric_worst_abs"]["path"],
                         "$.C1.measured_over_predicted")

    def test_runtime_and_provenance_do_not_make_a_rerun_differ(self):
        a = self._doc("aaa", 1.0, True)
        b = self._doc("bbb", 1.0, True)
        b["runtime_sec"] = 4001.9
        d = harness.compare_json(a, b)
        self.assertTrue(d["identical"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
