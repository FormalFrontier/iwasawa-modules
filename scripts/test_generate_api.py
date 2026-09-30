#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Data-only native-record corruption controls, not a proof or release audit.

Adapted for Iwasawa Modules from the accepted finite-group Tate cohomology
adapter, itself drawing on polynomial-root-stability and Anchor's
ideal-completion adapter. The native catalogue and Iwasawa adapter/tests are
a distinct Formal Frontier contribution; the donor retains credit for its
earlier expression. See docs/README.md for origins and limitations.
Supply eleven retained genuine native records; none is shipped by these tests.
"""

import argparse
import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import generate_api as api


ROOT = Path(__file__).resolve().parent.parent
PARSER = argparse.ArgumentParser(description=__doc__)
PARSER.add_argument("--native-data", type=Path, required=True)


class NativeControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources = {path: (ROOT / path).read_bytes() for path in api.SOURCE_INPUT_SHA256}
        cls.original = {
            module: (ARGS.native_data / ("declaration-data-" + module + ".bmp")).read_bytes()
            for module in api.MODULES
        }
        cls.records = {module: json.loads(raw) for module, raw in cls.original.items()}
        api.check_snapshot(api.SOURCE, cls.sources)
        api.validate(cls.records, cls.original, cls.sources, api.SOURCE)

    def corrupt(self, modify, expected):
        records = copy.deepcopy(self.records)
        sources = dict(self.sources)
        modify(records, sources)
        raw = {module: json.dumps(record, ensure_ascii=False, sort_keys=True,
                                  separators=(",", ":")).encode("utf-8")
               for module, record in records.items()}
        with self.assertRaisesRegex(ValueError, expected):
            api.render(records, raw, sources, api.SOURCE)

    def test_exact_unmodified_native_inputs_and_manifest(self):
        markdown, manifest_raw = api.render(self.records, self.original, self.sources, api.SOURCE)
        manifest = json.loads(manifest_raw)
        self.assertEqual(len(manifest["production_declarations"]), 54)
        self.assertEqual(len(manifest["public_client_declarations"]), 0)
        self.assertEqual(set(manifest["instance_declarations"]),
                         {name for table in api.EXPECTED_INSTANCES.values() for name in table})
        self.assertEqual(manifest["undocumented_count"], 2)
        self.assertEqual(markdown.count(b"\n#### `"), 54)
        self.assertEqual(len(manifest["modules"]), 11)
        self.assertEqual([manifest["module_inventory"][module]["declarations"]
                          for module in api.MODULES], list(api.COUNTS))
        self.assertEqual(sum(len(table) for table in manifest["native_instance_tables"].values()), 14)
        self.assertEqual(manifest["analyzed_source_revision"], api.SOURCE)
        self.assertEqual(manifest["analyzed_source_tree"], api.SOURCE_TREE)
        self.assertEqual(manifest["native_record_sha256"], api.NATIVE_RECORD_SHA256)
        self.assertEqual(manifest["inputs"], api.SOURCE_INPUT_SHA256)
        self.assertEqual(manifest["api_sha256"], api.digest(markdown))
        self.assertEqual((ROOT / "docs/API.md").read_bytes(), markdown)
        self.assertEqual((ROOT / "docs/api-manifest.json").read_bytes(), manifest_raw)
        self.assertNotIn(b"example.invalid", markdown + manifest_raw)
        self.assertNotIn(b"forgejo.vpn", markdown + manifest_raw)
        self.assertFalse(manifest["proof_certification"] or manifest["release_acceptance"])

    def test_missing_duplicate_extra_name_kind_source_and_instance_rows(self):
        module = api.MODULES[0]
        topology_module = api.MODULES[3]
        controls = [
            ("missing/extra native declaration", lambda records, sources: records[module]["declarations"].pop()),
            ("missing/extra native declaration", lambda records, sources: records[module]["declarations"].append(
                copy.deepcopy(records[module]["declarations"][0]))),
            ("duplicate native declaration", lambda records, sources: records[module]["declarations"].__setitem__(
                1, copy.deepcopy(records[module]["declarations"][0]))),
            ("native module name differs", lambda records, sources: records[module].__setitem__("name", "Other")),
            ("wrong native name/kind", lambda records, sources: records[module]["declarations"][0]["info"].__setitem__(
                "name", "Imported.Theorem")),
            ("wrong native name/kind", lambda records, sources: records[module]["declarations"][0]["info"].__setitem__(
                "kind", "axiom")),
            ("native source module/revision/path differs", lambda records, sources: records[module]["declarations"][0]["info"].__setitem__(
                "sourceLink", "https://example.invalid/commit/main/Norm.lean")),
            ("native self link differs", lambda records, sources: records[module]["declarations"][0]["info"].__setitem__(
                "docLink", "./other.html#name")),
            ("missing/extra/wrong native instance table", lambda records, sources: records[topology_module]["instances"].pop()),
            ("duplicate native instance row", lambda records, sources: records[topology_module]["instances"].append(
                copy.deepcopy(records[topology_module]["instances"][0]))),
            ("missing/extra/wrong native instance table", lambda records, sources: records[topology_module]["instances"][0].__setitem__(
                "className", "CategoryTheory.Other")),
            ("missing/extra/wrong native instance table", lambda records, sources: records[topology_module]["instances"][0].__setitem__(
                "typeNames", ["Other"])),
            ("native source docstring position differs", lambda records, sources: records[module]["declarations"][0]["info"].__setitem__(
                "line", 1)),
            ("missing/extra native declaration", lambda records, sources: records[api.MODULES[8]]["declarations"].append(
                copy.deepcopy(records[module]["declarations"][0]))),
        ]
        for diagnostic, change in controls:
            with self.subTest(diagnostic=diagnostic):
                self.corrupt(change, diagnostic)

    def test_active_html_and_implicit_binders(self):
        basic_module = api.MODULES[0]
        topology_module = api.MODULES[3]
        for fragment in ("<script>alert(1)</script>", "<img src='x'>", "<a href='javascript:evil'>x</a>",
                         "<span onclick='evil'>x</span>", "<div><span></div>"):
            with self.subTest(fragment=fragment):
                self.corrupt(lambda records, sources: records[basic_module]["declarations"][0].__setitem__("header", fragment),
                             "native header")
        self.corrupt(lambda records, sources: records[basic_module]["declarations"][0]["info"].__setitem__(
            "doc", "<script>alert(1)</script>"), "active/unsupported native docstring")
        binders = (
            ("Module.IsPseudoNull", "(M : Type u_2)", basic_module, ("Type</a> u_2)", "Type</a> z)")),
            ("LinearMap.IsPseudoIsomorphism.comp", "{P : Type u_1}", api.MODULES[1],
             ("Type</a> u_1}", "Type</a> z}")),
            ("CompletedGroupAlgebra.finiteGroupAlgebraRingTopology", "[Group H]", topology_module,
             ('<span class="fn">Group</span> <span class="fn">H</span>',
              '<span class="fn">Group</span> <span class="fn">Z</span>')),
            ("CompletedGroupAlgebra.instTopologicalSpace", "[TopologicalSpace R]", topology_module,
             ('<span class="fn">TopologicalSpace</span> <span class="fn">R</span>',
              '<span class="fn">TopologicalSpace</span> <span class="fn">Z</span>')),
            ("CompletedGroupAlgebra.instCompleteSpace", "[T2Space R]", api.MODULES[6],
             ('<span class="fn">T2Space</span> <span class="fn">R</span>',
              '<span class="fn">T2Space</span> <span class="fn">Z</span>')),
        )
        for name, token, module, replacement in binders:
            with self.subTest(binder=name + "/" + token):
                def remove_binder(records, sources):
                    row = next(row for row in records[module]["declarations"]
                               if row["info"]["name"] == name)
                    self.assertIn(token, api.Header(row["header"]).rendered())
                    self.assertIn(replacement[0], row["header"])
                    row["header"] = row["header"].replace(*replacement, 1)
                self.corrupt(remove_binder, "missing signature binder")

    def test_native_raw_bytes_docstrings_and_extra_file(self):
        module = api.MODULES[0]
        raw = dict(self.original)
        raw[module] += b" "
        with self.assertRaisesRegex(ValueError, "native raw record differs from pinned tool/input"):
            api.validate(self.records, raw, self.sources, api.SOURCE)
        self.corrupt(lambda records, sources: records[module]["declarations"][0]["info"].__setitem__(
            "doc", "Invented source docstring"), "native docstring/source mismatch")
        self.corrupt(lambda records, sources: records[api.MODULES[2]]["declarations"][0]["info"].__setitem__(
            "line", 1), "native source docstring position differs")
        with tempfile.TemporaryDirectory() as temporary:
            for name, data in self.original.items():
                (Path(temporary) / ("declaration-data-" + name + ".bmp")).write_bytes(data)
            (Path(temporary) / "declaration-data-Unapproved.Extra.bmp").write_bytes(b"{}")
            result = subprocess.run([sys.executable, "-B", str(ROOT / "scripts/generate_api.py"),
                                     "--native-data", temporary, "--source-revision", api.SOURCE,
                                     "--docgen-revision", api.TOOL, "--check"],
                                    capture_output=True, text=True, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("missing/extra native record file", result.stderr)

    def test_fixed_source_and_no_git_or_optimized_weakening(self):
        for path in self.sources:
            with self.subTest(path=path):
                changed = dict(self.sources)
                changed[path] += b"\n"
                with self.assertRaisesRegex(ValueError, "source/pin drift from accepted input"):
                    api.check_snapshot(api.SOURCE, changed)
        with self.assertRaisesRegex(ValueError, "source/pin inventory differs"):
            api.check_snapshot(api.SOURCE, {**self.sources, "extra.lean": b""})
        with self.assertRaisesRegex(ValueError, "unexpected/stale analyzed source revision"):
            api.check_snapshot("main", self.sources)
        with tempfile.TemporaryDirectory() as temporary:
            before = ((ROOT / "docs/API.md").read_bytes(),
                      (ROOT / "docs/api-manifest.json").read_bytes())
            result = subprocess.run([sys.executable, "-O", str(ROOT / "scripts/generate_api.py"),
                                     "--native-data", temporary, "--source-revision", api.SOURCE,
                                     "--docgen-revision", api.TOOL],
                                    capture_output=True, text=True, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("optimized Python is not supported", result.stderr)
            self.assertEqual(list(Path(temporary).iterdir()), [])
            self.assertEqual(before, ((ROOT / "docs/API.md").read_bytes(),
                                      (ROOT / "docs/api-manifest.json").read_bytes()))

    def test_source_only_archive_replay_without_git_executable(self):
        with tempfile.TemporaryDirectory() as temporary:
            archive = Path(temporary) / "source-archive"
            (archive / "scripts").mkdir(parents=True)
            (archive / "docs").mkdir()
            for path in api.SOURCE_INPUT_SHA256:
                target = archive / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(self.sources[path])
            for name in ("scripts/generate_api.py", "docs/API.md", "docs/api-manifest.json"):
                (archive / name).write_bytes((ROOT / name).read_bytes())
            native = Path(temporary) / "retained-native-inputs"
            native.mkdir()
            for module, raw in self.original.items():
                (native / ("declaration-data-" + module + ".bmp")).write_bytes(raw)
            command = [sys.executable, "-I", "-B", str(archive / "scripts/generate_api.py"),
                       "--native-data", str(native), "--source-revision", api.SOURCE,
                       "--docgen-revision", api.TOOL, "--check"]
            result = subprocess.run(command, cwd=archive, env={"PATH": "/no-git-binary"},
                                    capture_output=True, text=True, check=False)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('"status": "matched"', result.stdout)
            (archive / "docs/api-manifest.json").write_bytes(b"{}")
            result = subprocess.run(command, cwd=archive, env={"PATH": "/no-git-binary"},
                                    capture_output=True, text=True, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("generated file differs/stale manifest", result.stderr)
            (archive / "docs/api-manifest.json").write_bytes((ROOT / "docs/api-manifest.json").read_bytes())
            (archive / "docs/API.md").write_bytes(b"# stale\n")
            result = subprocess.run(command, cwd=archive, env={"PATH": "/no-git-binary"},
                                    capture_output=True, text=True, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("generated file differs/stale manifest: API.md", result.stderr)
            self.assertEqual((archive / "docs/API.md").read_bytes(), b"# stale\n")

    def test_isolated_parentless_same_tree_without_historical_object(self):
        tracked = subprocess.run(["git", "-C", str(ROOT), "ls-files", "-z"],
                                 capture_output=True, check=True).stdout
        paths = {entry.decode() for entry in tracked.split(b"\0") if entry}
        self.assertEqual(paths, {
            ".forgejo/lean-ci.json", ".forgejo/workflows/lean-ci.yaml", ".gitignore",
            "IwasawaModules.lean", "IwasawaModules/CompletedGroupAlgebra/Basic.lean",
            "IwasawaModules/CompletedGroupAlgebra/Compactness.lean",
            "IwasawaModules/CompletedGroupAlgebra/Completeness.lean",
            "IwasawaModules/CompletedGroupAlgebra/Separation.lean",
            "IwasawaModules/CompletedGroupAlgebra/Topology.lean",
            "IwasawaModules/PseudoIsomorphism/Basic.lean",
            "IwasawaModules/PseudoIsomorphism/LinearMap.lean", "IwasawaModulesTests.lean",
            "IwasawaModulesTests/DirectAPI.lean", "IwasawaModulesTests/RootAPI.lean",
            "LICENSE", "README.md", "docs/API.md", "docs/README.md",
            "docs/api-manifest.json", "formalization.yaml", "lake-manifest.json",
            "lakefile.toml", "lean-toolchain", "scripts/generate_api.py",
            "scripts/test_generate_api.py",
        })
        with tempfile.TemporaryDirectory() as temporary:
            isolated = Path(temporary) / "isolated"
            isolated.mkdir()
            for name in paths:
                source = ROOT / name
                self.assertTrue(source.is_file() and not source.is_symlink())
                target = isolated / name
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(source, target)
            environment = {"PATH": os.environ["PATH"],
                           "HOME": temporary,
                           "GIT_CONFIG_GLOBAL": "/dev/null",
                           "GIT_CONFIG_SYSTEM": "/dev/null",
                           "GIT_AUTHOR_NAME": "Formal Frontier Worker B",
                           "GIT_AUTHOR_EMAIL": "formalization-worker-b@agents.formalfrontier.com",
                           "GIT_COMMITTER_NAME": "Formal Frontier Worker B",
                           "GIT_COMMITTER_EMAIL": "formalization-worker-b@agents.formalfrontier.com"}
            for arguments in (["init", "-q"], ["add", "--all"],
                              ["commit", "-qm", "Parentless same-tree replay"]):
                subprocess.run(["git", "-C", str(isolated), *arguments], env=environment,
                               capture_output=True, check=True)
            sha = subprocess.run(["git", "-C", str(isolated), "rev-list", "--parents", "HEAD"],
                                 env=environment, capture_output=True, text=True, check=True).stdout.strip()
            self.assertEqual(len(sha.split()), 1)
            missing = subprocess.run(["git", "-C", str(isolated), "cat-file", "-e",
                                      api.SOURCE + "^{commit}"], env=environment,
                                     capture_output=True, check=False)
            self.assertNotEqual(missing.returncode, 0)
            tree = subprocess.run(["git", "-C", str(isolated), "ls-tree", "-r", "--name-only",
                                   "HEAD"], env=environment, capture_output=True,
                                  text=True, check=True).stdout.splitlines()
            self.assertEqual(set(tree), paths)
            for name in paths:
                self.assertEqual((isolated / name).read_bytes(), (ROOT / name).read_bytes())
            native = ARGS.native_data.resolve()
            result = subprocess.run([sys.executable, "-I", "-B", str(isolated / "scripts/generate_api.py"),
                                     "--native-data", str(native), "--source-revision", api.SOURCE,
                                     "--docgen-revision", api.TOOL, "--check"],
                                    cwd=isolated, env={"PATH": "/no-git-binary"},
                                    capture_output=True, text=True, check=False)
            self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == "__main__":
    ARGS = PARSER.parse_args()
    unittest.main(argv=[sys.argv[0]], verbosity=2)
