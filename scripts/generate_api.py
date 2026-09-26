#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Bounded native doc-gen4 reference for the Iwasawa Modules public surface.

Adapted by Task hive-request-5fc39d37ccb1adb18e0c62309771c4ccbe2140fa
(UID 645fd9e7-83b8-4288-ac17-54d375560cd6) from finite-group-tate-cohomology
61577f7cf2e02715f621a724aa692921ab6bbad9 (Task
381dc6f93292eb39ea2d5b25f09baacdc8b20d9e / UID
cd8c84f8-2dbf-4399-9c70-1de364ffa99f), itself adapted from
polynomial-root-stability 95ac896f81a3190b2634a4246a3e924d2a267a61
and Anchor's ideal-completion f0c8c34386109116e4912fb425a8ad15d9dc42a4.
Records are documentation input, not a proof, private-proof census, coverage or
release certificate.
"""

if not __debug__:
    raise SystemExit("optimized Python is not supported for API generation")

import argparse
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re


TOOL = "97d4ecdfc8e09e7f511724c25e303d448de6a3db"
SOURCE = "deceb449133f8bcc7fb4829e4fc167b483eef3a2"
SOURCE_TREE = "d039dbb6f4cc48f9c2160583d18531a604a1c114"
MODULES = ('IwasawaModules.PseudoIsomorphism.Basic',
 'IwasawaModules.PseudoIsomorphism.LinearMap',
 'IwasawaModules.CompletedGroupAlgebra.Basic',
 'IwasawaModules.CompletedGroupAlgebra.Topology',
 'IwasawaModules.CompletedGroupAlgebra.Separation',
 'IwasawaModules.CompletedGroupAlgebra.Compactness',
 'IwasawaModules.CompletedGroupAlgebra.Completeness',
 'IwasawaModules',
 'IwasawaModulesTests.RootAPI',
 'IwasawaModulesTests.DirectAPI',
 'IwasawaModulesTests')
SOURCE_INPUT_SHA256 = {'IwasawaModules/PseudoIsomorphism/Basic.lean': '371bd4997b9e561a67e81db1de9309e8f5c4b27ce59ce57791e1d5aa863f41de',
 'IwasawaModules/PseudoIsomorphism/LinearMap.lean': 'ee436362a2b31a7bb175d7267707e480fd17a04a1b88810214cf2579ef4b7005',
 'IwasawaModules/CompletedGroupAlgebra/Basic.lean': '99a12122e47c37bfbb913c8faeebe697db5bd9af4b09386f1a6e26705b618f39',
 'IwasawaModules/CompletedGroupAlgebra/Topology.lean': '06c8deb3d460f78b26efc13a76f649c9f21ea7ce4865c7fc014a28562ffb64eb',
 'IwasawaModules/CompletedGroupAlgebra/Separation.lean': '12fa0f1c3d7242ffb3abbe9023802820e21c8f891e4a7a09f52039e3c3f0d48f',
 'IwasawaModules/CompletedGroupAlgebra/Compactness.lean': 'ce36f43453ad2a2249ade1247b9fe61343dc95935425c69a03fcb9ad4370397d',
 'IwasawaModules/CompletedGroupAlgebra/Completeness.lean': '272590eb1859d66fdbc036f3b649ff90ad10974ece58727020903ffa5a04cb15',
 'IwasawaModules.lean': '246157cbd7e6e90c5edba3309950e9399bbc0de533e3cd13a5da4349b0392833',
 'IwasawaModulesTests/RootAPI.lean': 'abf65dbd4a53bfa59acecac757f8bd807946267668274cb934f75428de659858',
 'IwasawaModulesTests/DirectAPI.lean': '2a5ff40e5253f2109c50d02c3ce68ee35faf197ef89174a926460e911d4f1631',
 'IwasawaModulesTests.lean': '8a0592e7268a6ec062b4a6ced6b3599564754fc3cd3b030a3b2a22250ecc131f',
 'lean-toolchain': '8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88',
 'lakefile.toml': 'ec50272d45039e4f4c2c1e5bfb8e068f0206249634281cb93baeabb41134cb05',
 'lake-manifest.json': '8326635acea81d37f4d3b87363ded441be9b8503e939c71a60fd283ce1bdb880'}
NATIVE_RECORD_SHA256 = {'IwasawaModules.PseudoIsomorphism.Basic': 'd4d3f35c2c0dda717882eec297e93d5162c9183e6420704a8d610e2898a2ce57',
 'IwasawaModules.PseudoIsomorphism.LinearMap': 'a7059462de2544e7453928714299395ac82716c5393f73d62b2b4753eed1737e',
 'IwasawaModules.CompletedGroupAlgebra.Basic': '47c326dafca920f19f54a34faf6188c84bd95f0172c97c3f42a611a9cff3a9c6',
 'IwasawaModules.CompletedGroupAlgebra.Topology': 'c91721381c0d2b657cc3f0fecfa3059699b61d2491b7a5b135439909834b54f6',
 'IwasawaModules.CompletedGroupAlgebra.Separation': '482c8896eb801528be0c062055e85cfcd1b535bd30a9353cb182bfa62cbe64bd',
 'IwasawaModules.CompletedGroupAlgebra.Compactness': '03f37b750ac7a62680760bd227579077a0d91b03c77dc0ee5544bafc86a1e5f2',
 'IwasawaModules.CompletedGroupAlgebra.Completeness': '88659c1558ede2259746277fae2e168c90e8ff8d290e59f29c3b53fde0189da5',
 'IwasawaModules': '9e0b3c55e256951c9a29a06aafb6788cfbbf2548e29893dddcf08294817e1101',
 'IwasawaModulesTests.RootAPI': '99809b21d26908ba40f9f3cfe84c4c1fb838dc321fcdf7eaee26f187ab83c5e8',
 'IwasawaModulesTests.DirectAPI': '6a896953f3b06c786d41cb1e71983eba02eb612a2b84256fa39bd2238b41ef76',
 'IwasawaModulesTests': 'f3720464b12a257347404b53d5668a03db0f363f0abedef0a6da9fc5f0533330'}
COUNTS = (9, 8, 10, 12, 2, 3, 10, 0, 0, 0, 0)
EXPECTED_INSTANCES = {'IwasawaModules.PseudoIsomorphism.Basic': {},
 'IwasawaModules.PseudoIsomorphism.LinearMap': {},
 'IwasawaModules.CompletedGroupAlgebra.Basic': {},
 'IwasawaModules.CompletedGroupAlgebra.Topology': {'CompletedGroupAlgebra.instTopologicalSpaceFiniteGroupAlgebra': ('TopologicalSpace',
                                                                                                                    ('MonoidAlgebra',)),
                                                   'CompletedGroupAlgebra.instIsTopologicalRingFiniteGroupAlgebra': ('IsTopologicalRing',
                                                                                                                     ('MonoidAlgebra',)),
                                                   'CompletedGroupAlgebra.instTopologicalSpace': ('TopologicalSpace',
                                                                                                  ('RingCat.carrier',)),
                                                   'CompletedGroupAlgebra.instIsTopologicalRing': ('IsTopologicalRing',
                                                                                                   ('RingCat.carrier',))},
 'IwasawaModules.CompletedGroupAlgebra.Separation': {'CompletedGroupAlgebra.instT2SpaceFiniteGroupAlgebra': ('T2Space',
                                                                                                             ('MonoidAlgebra',)),
                                                     'CompletedGroupAlgebra.instT2Space': ('T2Space',
                                                                                           ('RingCat.carrier',))},
 'IwasawaModules.CompletedGroupAlgebra.Compactness': {'CompletedGroupAlgebra.instCompactSpaceFiniteGroupAlgebra': ('CompactSpace',
                                                                                                                   ('MonoidAlgebra',)),
                                                      'CompletedGroupAlgebra.instCompactSpace': ('CompactSpace',
                                                                                                 ('RingCat.carrier',))},
 'IwasawaModules.CompletedGroupAlgebra.Completeness': {'CompletedGroupAlgebra.instUniformSpaceFiniteGroupAlgebra': ('UniformSpace',
                                                                                                                    ('MonoidAlgebra',)),
                                                       'CompletedGroupAlgebra.instIsUniformAddGroupFiniteGroupAlgebra': ('IsUniformAddGroup',
                                                                                                                         ('MonoidAlgebra',)),
                                                       'CompletedGroupAlgebra.instCompleteSpaceFiniteGroupAlgebra': ('CompleteSpace',
                                                                                                                     ('MonoidAlgebra',)),
                                                       'CompletedGroupAlgebra.instUniformSpace': ('UniformSpace',
                                                                                                  ('RingCat.carrier',)),
                                                       'CompletedGroupAlgebra.instIsUniformAddGroup': ('IsUniformAddGroup',
                                                                                                       ('RingCat.carrier',)),
                                                       'CompletedGroupAlgebra.instCompleteSpace': ('CompleteSpace',
                                                                                                   ('RingCat.carrier',))},
 'IwasawaModules': {},
 'IwasawaModulesTests.RootAPI': {},
 'IwasawaModulesTests.DirectAPI': {},
 'IwasawaModulesTests': {}}
KINDS = ("def", "theorem", "instance")
NAME_PREFIXES = {
    "IwasawaModules.PseudoIsomorphism.Basic": ("Module.", "LinearEquiv."),
    "IwasawaModules.PseudoIsomorphism.LinearMap": ("LinearMap.", "LinearEquiv."),
    **{module: ("CompletedGroupAlgebra.",) for module in MODULES[2:7]},
}
KEY_TOKENS = {
    "Module.IsPseudoNull": ("(R : Type u_1)", "(M : Type u_2)", "[CommRing R]"),
    "LinearMap.IsPseudoIsomorphism": ("{M : Type v}", "{N : Type w}", "(f : M →ₗ[R] N)"),
    "LinearMap.IsPseudoIsomorphism.comp": ("{M : Type v}", "{N : Type w}", "{P : Type u_1}"),
    "CompletedGroupAlgebra": ("(R : Type u)", "(G : ProfiniteGrp.{v})", "RingCat"),
    "CompletedGroupAlgebra.finiteGroupAlgebraCoefficients": ("(H : Type v)", "[Finite H]"),
    "CompletedGroupAlgebra.finiteGroupAlgebraRingTopology": ("[Group H]", "[IsTopologicalRing R]"),
    "CompletedGroupAlgebra.instTopologicalSpace": ("[TopologicalSpace R]", "(G : ProfiniteGrp.{v})"),
    "CompletedGroupAlgebra.instCompactSpaceFiniteGroupAlgebra": ("[CompactSpace R]", "[Finite H]"),
    "CompletedGroupAlgebra.instCompactSpace": ("[CompactSpace R]", "[T2Space R]"),
    "CompletedGroupAlgebra.instCompleteSpaceFiniteGroupAlgebra": ("[CompactSpace R]", "[Group H]"),
    "CompletedGroupAlgebra.instCompleteSpace": ("[CompactSpace R]", "[T2Space R]"),
}
CATALOGUE = {
    "proj_ofMonoidAlgebra": "The ordinary-to-completed homomorphism reduces at each finite quotient to the group-algebra map induced by the quotient homomorphism.",
    "ext_iff": "The `@[ext]`-generated equivalence says that completed elements agree exactly when all their finite-quotient projections agree; its source is the preceding `ext` theorem.",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


class Header(HTMLParser):
    """Extract all visible native tokens, including hidden-by-CSS implicits."""

    def __init__(self, value):
        super().__init__(convert_charrefs=True)
        self.stack = []
        self.text = []
        self.kinds = []
        self.names = []
        self.feed(value)
        self.close()
        require(not self.stack, "unclosed native header")

    def handle_starttag(self, tag, attrs):
        require(tag in {"div", "span", "a"}, "unexpected/active native header tag")
        attributes = dict(attrs)
        require(len(attrs) == len(attributes) and set(attributes) <= {"class", "href"},
                "active/unknown native header attribute")
        require(tag == "a" or "href" not in attributes, "unexpected native header link")
        require("href" not in attributes or
                re.fullmatch(r"\./[\w./#-]+", attributes["href"]) is not None,
                "active/external native header link")
        classes = set(attributes.get("class", "").split())
        if tag == "div" and "decl_type" in classes:
            self.text.append(" ")
        self.stack.append((tag, classes))

    def handle_endtag(self, tag):
        require(bool(self.stack) and self.stack[-1][0] == tag, "unbalanced native header")
        self.stack.pop()

    def handle_data(self, value):
        require(bool(self.stack) or not value.strip(), "text outside native header")
        self.text.append(value)
        if any("decl_kind" in classes for _, classes in self.stack):
            self.kinds.append(value)
        if any("decl_name" in classes for _, classes in self.stack):
            self.names.append(value)

    def handle_comment(self, _):
        raise ValueError("unexpected native header comment")

    def handle_decl(self, _):
        raise ValueError("unexpected native header declaration")

    def rendered(self):
        return " ".join("".join(self.text).split())


def source_anchor(raw, line, name, doc):
    lines = raw.decode("utf-8").splitlines()
    require(type(line) is int and 0 < line <= len(lines), "invalid native source line: " + name)
    rest = "\n".join(lines[line - 1:])
    if doc:
        require(rest.startswith("/--"), "native source docstring position differs: " + name)
        source_doc, closing, rest = rest.partition("-/")
        require(bool(closing) and source_doc[3:].strip() == doc.strip(),
                "native docstring/source mismatch: " + name)
    else:
        require(not rest.startswith("/--"), "native docstring missing: " + name)
    declaration = re.search(r"(?m)^[ \t]*(?:@\[[^\n]*?\][ \t]*)*"
                            r"(?:(?:noncomputable|private|protected)[ \t]+)?"
                            r"(def|lemma|theorem|instance|abbrev)[ \t]+(\S+)", rest)
    require(declaration is not None, "native source declaration absent: " + name)
    source_name = name
    for namespace in ("Module.", "LinearMap.", "LinearEquiv.", "CompletedGroupAlgebra."):
        source_name = source_name.removeprefix(namespace)
    if name == "CompletedGroupAlgebra.ext_iff":
        require(rest.startswith("@[ext]"), "generated extensionality source differs")
        source_name = "ext"
    require(declaration.group(2).removeprefix("_root_.") == source_name and
            "/--" not in rest[:declaration.start()], "native source/name position differs: " + name)


def check_snapshot(revision, sources):
    require(revision == SOURCE, "unexpected/stale analyzed source revision")
    require(set(sources) == set(SOURCE_INPUT_SHA256), "source/pin inventory differs")
    for path, expected in SOURCE_INPUT_SHA256.items():
        require(digest(sources[path]) == expected, "source/pin drift from accepted input: " + path)


def validate(records, raw_records, sources, revision):
    check_snapshot(revision, sources)
    require(set(records) == set(raw_records) == set(MODULES), "native module inventory differs")
    sections = {"production": [], "clients": []}
    all_names = set()
    undocumented = set()
    for module, expected_count in zip(MODULES, COUNTS):
        record = records[module]
        require(json.loads(raw_records[module]) == record,
                "native record bytes/JSON differ: " + module)
        require(type(record) is dict and set(record) == {"name", "declarations", "instances", "imports"},
                "native module shape differs: " + module)
        require(record["name"] == module, "native module name differs: " + module)
        require(type(record["declarations"]) is list and len(record["declarations"]) == expected_count,
                "missing/extra native declaration: " + module)
        require(type(record["instances"]) is list and type(record["imports"]) is list,
                "native instances/imports shape differs: " + module)
        instance_names = {}
        for instance in record["instances"]:
            require(type(instance) is dict and set(instance) == {"name", "className", "typeNames"}
                    and type(instance["name"]) is str and type(instance["className"]) is str
                    and type(instance["typeNames"]) is list and
                    all(type(item) is str for item in instance["typeNames"]),
                    "malformed native instance row")
            require(instance["name"] not in instance_names, "duplicate native instance row")
            instance_names[instance["name"]] = (instance["className"], tuple(instance["typeNames"]))
        require(instance_names == EXPECTED_INSTANCES[module],
                "missing/extra/wrong native instance table: " + module)
        path = module.replace(".", "/") + ".lean"
        names = set()
        for row in record["declarations"]:
            require(type(row) is dict and set(row) == {"info", "header"}
                    and type(row["info"]) is dict,
                    "native declaration shape differs: " + module)
            info = row["info"]
            require(set(info) == {"name", "kind", "doc", "docLink", "sourceLink", "line"},
                    "native declaration info shape differs: " + module)
            name, kind = info["name"], info["kind"]
            require(type(name) is str and type(kind) is str and kind in KINDS and
                    (name.startswith(NAME_PREFIXES.get(module, ())) or
                     (module == "IwasawaModules.CompletedGroupAlgebra.Basic" and
                      name == "CompletedGroupAlgebra")),
                    "wrong native name/kind: " + str(name))
            require(name not in names and name not in all_names,
                    "duplicate native declaration: " + name)
            names.add(name)
            all_names.add(name)
            require(type(info["doc"]) is str and type(row["header"]) is str,
                    "malformed native doc/header: " + name)
            require(info["sourceLink"] == "https://example.invalid/commit/" + revision + "/" + path,
                    "native source module/revision/path differs: " + name)
            require(info["docLink"] == "./" + module.replace(".", "/") + ".html#" + name,
                    "native self link differs: " + name)
            require("```" not in info["doc"] and
                    re.search(r"<\s*[/!?a-zA-Z]", info["doc"]) is None,
                    "active/unsupported native docstring: " + name)
            source_anchor(sources[path], info["line"], name, info["doc"])
            header = Header(row["header"])
            visible_kind = "".join(header.kinds)
            text = header.rendered()
            require((visible_kind in {"def", "noncomputable def", "noncomputable abbrev", "abbrev"}
                     if kind == "def" else visible_kind in {kind, "noncomputable " + kind}) and
                    "".join(header.names) == name
                    and text.startswith(visible_kind + " " + name + " ") and
                    "```" not in text and "<script" not in text.lower(),
                    "native signature identity/format differs: " + name)
            for binder in KEY_TOKENS.get(name, ()):
                require(binder in text, "missing signature binder: " + name + " / " + binder)
            if kind == "instance":
                require(name in instance_names, "declaration/instance table mismatch: " + name)
            elif name in instance_names:
                raise ValueError("instance table kind mismatch: " + name)
            note = None
            if not info["doc"]:
                short_name = name.rsplit(".", 1)[-1]
                require(short_name in CATALOGUE and kind == "theorem",
                        "missing original catalogue explanation: " + name)
                note = CATALOGUE[short_name]
                undocumented.add((module, name))
            section = "clients" if module.startswith("IwasawaModulesTests") else "production"
            sections[section].append(dict(name=name, kind=kind, path=path,
                                          line=info["line"], signature=text,
                                          doc=info["doc"].strip(), note=note))
        require(set(instance_names) == {row["info"]["name"] for row in record["declarations"]
                                        if row["info"]["kind"] == "instance"},
                "missing native instance declaration: " + module)
        require(digest(raw_records[module]) == NATIVE_RECORD_SHA256[module],
                "native raw record differs from pinned tool/input: " + module)
    require(len(all_names) == 54 and len(sections["production"]) == 54 and
            len(sections["clients"]) == 0 and undocumented == {
                ("IwasawaModules.CompletedGroupAlgebra.Basic", "CompletedGroupAlgebra.ext_iff"),
                ("IwasawaModules.CompletedGroupAlgebra.Basic", "CompletedGroupAlgebra.proj_ofMonoidAlgebra")},
            "mixed public/client/undocumented inventory differs")
    return sections


def render(records, raw_records, sources, revision):
    sections = validate(records, raw_records, sources, revision)
    lines = ["# Native API reference", "",
             "Fixed Lean `v4.34.0-rc2`, mathlib `e37d88a26f3791ed5a93daa1f949af1021b8d103`",
             "and separately pinned doc-gen4 `" + TOOL + "`. Full displayed signatures",
             "retain all native implicit arguments, typeclasses and universe variables.",
             "The eleven native module records contain **54 production named declarations**:",
             "16 definitions (including an abbreviation), 24 theorems and 14 named instances.",
             "The production root, two test leaves and test root each export **zero**",
             "native named entries. The test source files still contain checked Lean clients;",
             "zero exported native records do not mean zero source-level tests.",
             "The filtered native tables do **not** enumerate implementation-private helpers,",
             "local compiler declarations or stored proof bodies; this is not a private-proof",
             "census. It does not certify axioms, proof integrity,",
             "source coverage, rights or a release. [Reproduce and assess provenance](README.md).", "",
             "Source links point only to the unchanged `.lean` files shipped here.",
             "**Native source docstring** reproduces a matched source comment;",
             "**Original catalogue explanation** is newly written here for an entry",
             "without a Lean docstring. `ext_iff` is generated from `@[ext]`.", "",
             "## Module and instance inventory", "",
             "| Native module | Definitions | Theorems | Named instances |", "| --- | ---: | ---: | ---: |"]
    for module in MODULES:
        counts = {kind: sum(row["info"]["kind"] == kind for row in records[module]["declarations"])
                  for kind in KINDS}
        lines.append("| [`" + module + "`](../" + module.replace(".", "/") + ".lean) | " +
                     " | ".join(str(counts[kind]) for kind in KINDS) + " |")
    lines.extend(["", "Native instance tables (name, class and type names):", ""])
    for module in MODULES:
        for instance in records[module]["instances"]:
            lines.append("- `" + instance["name"] + "`: `" + instance["className"] +
                         "` on `" + ", ".join(instance["typeNames"]) + "`.")
    lines.extend(["", "## Production named API", ""])
    for module in MODULES:
        if module.startswith("IwasawaModulesTests"):
            continue
        lines.extend(["### `" + module + "`", ""])
        rows = sorted((row for row in sections["production"]
                       if row["path"] == module.replace(".", "/") + ".lean"),
                      key=lambda item: (item["line"], item["name"]))
        if not rows:
            lines.extend(["Zero native named entries; this module reexports the production leaves.", ""])
        for row in rows:
            lines.extend(["#### `" + row["name"] + "`", "", "Kind: `" + row["kind"] + "`.", "",
                          "```lean", row["signature"], "```", ""])
            if row["note"] is None:
                lines.extend(["**Native source docstring:** " + row["doc"], ""])
            else:
                lines.extend(["**Original catalogue explanation (not a Lean docstring):** " +
                              row["note"], ""])
            lines.extend([f"[Source](../{row['path']}#L{row['line']}) "
                          "(native source start line; generated `ext_iff` points to `@[ext]`).", ""])
    lines.extend(["## Checked-use modules (zero exported native entries)", "",
                  "The [aggregate-root tests](../IwasawaModulesTests/RootAPI.lean) and",
                  "[direct-leaf tests](../IwasawaModulesTests/DirectAPI.lean) elaborate named",
                  "clients, including zero and nonzero coefficients, a noncommutative finite",
                  "group and an empty finite index. Their native records export zero named",
                  "declarations and zero instances. The [test root](../IwasawaModulesTests.lean)",
                  "also has zero native entries and imports both leaves; these test clients",
                  "are checked by the default Lake build, not exported through the",
                  "production aggregate root.", ""])
    markdown = "\n".join(lines).encode("utf-8")
    manifest = dict(format=2, generator="scripts/generate_api.py", docgen_revision=TOOL,
                    analyzed_source_revision=SOURCE, analyzed_source_tree=SOURCE_TREE,
                    modules=list(MODULES), inputs=SOURCE_INPUT_SHA256,
                    native_record_sha256=NATIVE_RECORD_SHA256,
                    normalized_record_sha256={module: digest(json.dumps(records[module],
                            ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8"))
                            for module in MODULES},
                    module_inventory={module: {"declarations": len(records[module]["declarations"]),
                                       "kinds": {kind: sum(row["info"]["kind"] == kind
                                                           for row in records[module]["declarations"])
                                                 for kind in KINDS},
                                       "instance_rows": len(records[module]["instances"])}
                                      for module in MODULES},
                    native_instance_tables={module: records[module]["instances"] for module in MODULES},
                    production_declarations=[row["name"] for row in sections["production"]],
                    public_client_declarations=[row["name"] for row in sections["clients"]],
                    instance_declarations=[name for module in MODULES
                                           for name in EXPECTED_INSTANCES[module]],
                    undocumented_count=2,
                    undocumented_declarations=["CompletedGroupAlgebra.ext_iff",
                                               "CompletedGroupAlgebra.proj_ofMonoidAlgebra"],
                    api_sha256=digest(markdown),
                    proof_certification=False, release_acceptance=False)
    return markdown, (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode("utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-data", type=Path, required=True)
    parser.add_argument("--source-revision", required=True)
    parser.add_argument("--docgen-revision", required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    require(args.docgen_revision == TOOL, "unexpected/stale doc-gen4 revision")
    root = Path(__file__).resolve().parent.parent
    sources = {}
    for path in SOURCE_INPUT_SHA256:
        source_path = root / path
        require(source_path.is_file() and not source_path.is_symlink(), "missing/linked source input: " + path)
        sources[path] = source_path.read_bytes()
    check_snapshot(args.source_revision, sources)
    require(args.native_data.is_dir() and not args.native_data.is_symlink(), "native data directory absent/linked")
    expected_files = {"declaration-data-" + module + ".bmp" for module in MODULES}
    files = set(path.name for path in args.native_data.iterdir())
    require(files == expected_files, "missing/extra native record file")
    raw_records = {}
    records = {}
    for module in MODULES:
        path = args.native_data / ("declaration-data-" + module + ".bmp")
        require(path.is_file() and not path.is_symlink(), "missing/linked native record: " + module)
        raw_records[module] = path.read_bytes()
        records[module] = json.loads(raw_records[module])
    api, manifest = render(records, raw_records, sources, args.source_revision)
    for name, raw in (("API.md", api), ("api-manifest.json", manifest)):
        target = root / "docs" / name
        if args.check:
            require(target.is_file() and not target.is_symlink() and target.read_bytes() == raw,
                    "generated file differs/stale manifest: " + name)
        else:
            require(not target.is_symlink(), "linked output refused: " + name)
    if not args.check:
        (root / "docs" / "API.md").write_bytes(api)
        (root / "docs" / "api-manifest.json").write_bytes(manifest)
    print(json.dumps(dict(status="matched" if args.check else "generated", production=54,
                          clients=0, instances=14, api_sha256=digest(api),
                          proof_certification=False, release_acceptance=False)))


if __name__ == "__main__":
    main()
