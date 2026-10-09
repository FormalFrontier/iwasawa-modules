# Native reference and reproduction

The [native API reference](API.md) and its [input/hash manifest](api-manifest.json)
cover all **eleven** Lean modules in the frozen mathematical input
`deceb449133f8bcc7fb4829e4fc167b483eef3a2` (tree
`d039dbb6f4cc48f9c2160583d18531a604a1c114`): seven production leaves,
the production reexport root, two test leaves and the test root. The native
records contain **54 production named entries** (16 definitions, 24 theorems,
14 instances). The reexport root and all three test modules each have **zero
exported native entries or instance rows**, even though the test leaves contain
build-checked Lean clients. The complete native instance tables and per-module
counts are in both the reference and manifest. These are actual filtered native
tables, not a count of source-level test cases or private proof declarations.
In each separately retained SQLite run, the tool's raw tables have **11**
`modules`, **54** `name_info`, **52** `declaration_markdown_docstrings`, **20**
`definition_equations`, **14** `instances` and **14** `instance_args` rows.
`internal_names`, `tactics`, `tactic_tags`, `structures` and `axioms` tables
each have **zero** rows for this run. The external evidence preserves all table
names, columns and counts, not just these selected figures. Zero rows in such
native tables do **not** establish absence of compiler-private declarations or
admitted/stored proof dependencies in the compiled Lean environment.

Two Basic.lean entries have no source docstring: `proj_ofMonoidAlgebra` and
the `@[ext]`-generated `ext_iff`. They have clearly labeled **original catalogue
explanations**, not invented Lean docstrings. Every other native entry's
docstring is matched to its original source comment. Displayed signatures
include otherwise CSS-collapsed implicit arguments, typeclasses and universes;
the six finite coefficientwise APIs without `Group H` and the distinct
compact/Hausdorff completeness hypotheses remain visible. This reference
filters out implementation-private compactness helpers and generated/local
proof bodies; it is **not** the full private-proof census, an axiom audit, a
source-coverage finding or a release certificate. Neither upstream dependency
docstrings nor the native website, HTML/JS/fonts or source-book assets ship.
The separate optional full-import `docBlameThm` diagnostic on this input finds
four undocstringed theorems: those two Basic.lean entries and the generated
`Module.IsPseudoNull.eq_1` and `LinearMap.IsPseudoIsomorphism.eq_1`. The latter
two are **not** exported in the eleven filtered native records. The ordinary
15-linter production/test checks pass; the optional linter finding remains
visible for independent disposition, not silently suppressed or fixed by this
documentation-only unit. Existing honest no-copyright-holder source headers
are frozen; a separate style-header warning asking for an “All rights
reserved” copyright line is not permission to invent ownership or rewrite
the header as part of these docs.

Historical supplemental source-style checks retained 27 header diagnostics across the nine
declaration-bearing leaves and two `privateModule` diagnostics on the test leaves.
The latter deliberately provide build-checked private clients, not a public test
API; making them public merely to silence this diagnostic would change that
boundary. These historical findings and their release-review dispositions are
not new linter passes. Strict source options passed on the production reexport
root. The import-only test root does not register `linter.mathlibStandardSet`;
its first strict-option invocation failed, while the documented weak-option
invocation passed. Weak options do not establish that an unregistered linter ran.
The pinned text-style tool checked all eleven modules and exited zero, retaining
its warning that the absent `scripts/nolints-style.txt` was treated as empty.
No suppressions, artificial ownership statements or source edits were added.

## Immutable analyzed inputs and external tool

The generator checks SHA-256 of **all eleven source modules and three pins**
(`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`), and requires exactly
eleven byte-pinned external raw native records. Their digests and normalized
JSON digests appear in the [manifest](api-manifest.json). The analyzed commit
and tree are labels for these fixed **mathematical/pinned inputs**, not claims
that a later documentation commit or a source-only archive has the old Git
object. Each published snapshot has its own exact release record; a new
documentation candidate needs its own independent review and acceptance.

The separately built upstream `leanprover/doc-gen4` source revision is
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, tree
`ebf77f3e174c145c9ca2db0df1c18a78ae87c93b`, using its own pinned Lean
`v4.34.0-rc2`. It is **not** a dependency of the Iwasawa Modules project;
it is a separate core-only documentation tool. The library's pinned mathlib
revision is `e37d88a26f3791ed5a93daa1f949af1021b8d103`.

Before any project build, install the pinned toolchain and successfully fetch
the matching mathlib cache *in that checkout*. Cache failure is a blocker, not
permission to rebuild mathlib from source. One bounded build recipe is:

```sh
elan toolchain install "$(cat lean-toolchain)"
lake exe cache get
LEAN_NUM_THREADS=2 lake --wfail build
```

The default build already includes both production and test roots. An explicit
second-root build is an optional diagnostic, not a duplicate required build.

In a separate doc-gen4 checkout, verify the tool revision/tree and run
`lake build doc-gen4` there. If `cc` is not in your shell's `PATH`, use
`PATH="$(dirname "$(elan which lean)"):$PATH" lake build doc-gen4` there;
the pinned Lean installation supplies a compiler wrapper. From the library
root, with that built executable and a **fresh external directory**:

```bash
TOOL=/path/to/separate/doc-gen4/.lake/build/bin/doc-gen4
OUT=/path/to/fresh/native-output
REV=deceb449133f8bcc7fb4829e4fc167b483eef3a2
modules=(IwasawaModules.PseudoIsomorphism.Basic
  IwasawaModules.PseudoIsomorphism.LinearMap
  IwasawaModules.CompletedGroupAlgebra.Basic
  IwasawaModules.CompletedGroupAlgebra.Topology
  IwasawaModules.CompletedGroupAlgebra.Separation
  IwasawaModules.CompletedGroupAlgebra.Compactness
  IwasawaModules.CompletedGroupAlgebra.Completeness
  IwasawaModules IwasawaModulesTests.RootAPI
  IwasawaModulesTests.DirectAPI IwasawaModulesTests)
mkdir -p "$OUT/build" "$OUT/render" "$OUT/native-input"
for module in "${modules[@]}"; do
  path="${module//.//}.lean"
  LEAN_NUM_THREADS=2 lake env "$TOOL" single --build "$OUT/build" "$module" \
    "$OUT/build/api.db" "https://example.invalid/commit/$REV/$path"
done
"$TOOL" bibPrepass --build "$OUT/render" --none
"$TOOL" fromDb --build "$OUT/render" --manifest "$OUT/render/manifest.json" \
  "$OUT/build/api.db" "${modules[@]}"
for module in "${modules[@]}"; do
  cp "$OUT/render/doc-data/declaration-data-$module.bmp" "$OUT/native-input/"
done
python3 -B scripts/test_generate_api.py --native-data "$OUT/native-input"
python3 -B scripts/generate_api.py --native-data "$OUT/native-input" \
  --source-revision "$REV" \
  --docgen-revision 97d4ecdfc8e09e7f511724c25e303d448de6a3db --check
```

`example.invalid` is inert **native record identity**; generated Markdown
links exclusively to local Lean files. Copy only the eleven named records,
not any dependency-module records the tool also generates. Retain both native
SQLite databases, the eleven raw records per run, the commands, exit status,
full stdout/stderr and byte hashes outside the shipped tree for review.

The adapter rejects wrong/missing/extra module records, source/pin or tool
drift, duplicate/name/kind/line/source/docstring changes, wrong instance rows,
lost key binders, active/unknown HTML and stale generated files. All raw
record bytes are pinned, including formatting and native source links;
normalized hashes are **additional**, not a replacement. An optimized Python
invocation refuses before reading or writing. `--check` reads fixed inputs
without writing output. The controls exercise data corruption, a source-only
archive with no `git` executable, and an isolated parentless same-tree copy
without the historical analyzed Git object. Neither Git nor that historical
object is required for the adapter's replay; independent review still binds
the final committed tree, proof bodies and rights separately.

## Resource context and limits

On September 26, 2026, the pinned 8,892-object mathlib cache fetch succeeded
before warning-fatal default and all-eleven-module builds. A first default
build ran in **15.697 seconds**, followed by a **2.275-second** warm explicit
build, in a **15 GiB cgroup**. `LEAN_NUM_THREADS=2` controls Lean's runtime
threads but is **not** a cap on Lake jobs, total processes or memory;
`LAKE_JOBS=2` and `lake -Kjobs=2` are not verified scheduler limits in this
pinned Lake. The default-build sampled child-process-tree RSS reached
**3.70 GB**, while sampled *whole-cgroup* usage reached **14.17 GB**;
the latter includes cache/page residency. A simultaneous separate doc-gen4 build
was author-reported; the samples do not independently allocate usage between
projects, so this is **not an isolated project requirement**.
Individual native `single` calls sampled child-tree RSS of approximately
**3.8 GB** in this checkout, with cgroup usage around **13.5 GB**, again
including already resident dependency/cache pages. Samples are periodic,
not certified peaks or a portable benchmark. Plan aggregate headroom and
observe local cgroup/process use; don't translate child RSS into a memory
limit. Earlier selected checker calls failed with an artificial **9 GB
virtual-address-space** (`ulimit -v`) ceiling on mmap; this does not establish
a 9 GB physical-RAM requirement or proof failure. Build success and native
documentation do not replace the complete transitive standard-axiom audit,
including private and generated declarations, or independent review. Separate
stored-proof replay is not a release prerequisite.

The separate September 26 warm-use baseline for the [README's Lean example](../README.md#reproduce)
after cache and module builds measured **2.880 seconds** ordinary and **2.892
seconds** with `-T0` using `lake env lean -j1 -DwarningAsError=true`, one Lean
runtime thread and a **23 GiB cgroup**. Sampled process-group RSS was
**3,713,712,128 / 3,747,016,704 bytes** respectively. Both stdout/stderr were
empty; a 300-second timeout, 18 GiB sampled-RSS watchdog and 64 GiB virtual
address ceiling were configured bounds, not observed consumption or portable
minima. These timings do not establish a speedup over an earlier release.

## Expression, origins and rights

The original Iwasawa Modules Lean proofs/docstrings and separately contributed
clients are credited in the [project README](../README.md#credits-and-references).
The native adapter, its tests and two original catalogue explanations are a
distinct Formal Frontier contribution. Their expression was adapted under
Apache-2.0 from the accepted finite-group Tate cohomology adapter, itself
drawing on polynomial-root-stability and Anchor's ideal-completion adapter.
The donor's contributor retains credit for that earlier expression; this
adaptation does not attribute the Iwasawa catalogue to that donor. The
[project LICENSE](../LICENSE) remains unchanged, and collective **Authors:
Formal Frontier Agents** and named roles do not assert copyright ownership.
Imported mathlib APIs and the external doc-gen4 tool retain their upstream
notices. No book text, third-party proof code or native website assets are
bundled. Exact successor rights, history and release acceptance are separate
from this API catalogue.
