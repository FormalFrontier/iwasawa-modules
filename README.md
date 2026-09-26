# Iwasawa modules

Reusable Lean foundations for pseudo-null modules, directional
pseudo-isomorphisms and finite-quotient completed group algebras. **Authors:
Formal Frontier Agents. License: Apache-2.0.** See [LICENSE](LICENSE).

## Mathematical scope

For an arbitrary commutative ring, `Module.IsPseudoNull R M` means that the
support of `M` avoids every prime of height at most one. It is equivalent to
vanishing of those localizations and is stable under submodules, quotients and
short exact extensions. A *directional* pseudo-isomorphism is a linear map
whose kernel and cokernel are pseudo-null; it becomes bijective at all such
primes. Identities, bijective maps and composition are covered. Ring, source,
middle and target modules may live in independent universes. Neither finite
generation, Noetherianity nor a normal-domain assumption is built into these
predicates. No converse-by-reversing-arrows theorem is asserted.

`CompletedGroupAlgebra R G` is the `RingCat` limit of the ordinary group
algebras `R[G/U]` over open normal subgroups of the profinite group `G`.
`RingCat`, rather than `CommRingCat`, permits noncommutative quotient groups.
The library supplies coordinate projections, their compatibility and the
canonical map from `R[G]`, with no density or injectivity assertion about that
map. Finite-level topology is coefficientwise; the completed topology is
induced by its coordinates. A map into the completion is continuous exactly
when each coordinate is continuous. Coefficient Hausdorffness yields
Hausdorffness at finite and completed levels. Finite-level compactness requires
compact coefficients, **not** Hausdorffness; finite-level completeness uses a
topological ring with compact coefficients. The *completed* compactness and
canonical-additive-uniformity completeness route requires compact **and
Hausdorff** topological-ring coefficients. Completeness over coefficients that
are merely complete, compact-module structure, `Z_p[[Gamma]]` comparisons,
Iwasawa invariants, growth and adjoints are not established here.

## Modules and use

| Module | Public content |
| --- | --- |
| [`IwasawaModules/PseudoIsomorphism/Basic.lean`](IwasawaModules/PseudoIsomorphism/Basic.lean) | Support/localization pseudo-nullity and exact/subquotient closure |
| [`IwasawaModules/PseudoIsomorphism/LinearMap.lean`](IwasawaModules/PseudoIsomorphism/LinearMap.lean) | Directional maps, localized kernel/bijectivity, composition |
| [`IwasawaModules/CompletedGroupAlgebra/Basic.lean`](IwasawaModules/CompletedGroupAlgebra/Basic.lean) | `RingCat` limit, projections and ordinary map |
| [`IwasawaModules/CompletedGroupAlgebra/Topology.lean`](IwasawaModules/CompletedGroupAlgebra/Topology.lean) | Coefficientwise and inverse-limit topologies, continuity |
| [`IwasawaModules/CompletedGroupAlgebra/Separation.lean`](IwasawaModules/CompletedGroupAlgebra/Separation.lean) | Finite-level and completed Hausdorff instances |
| [`IwasawaModules/CompletedGroupAlgebra/Compactness.lean`](IwasawaModules/CompletedGroupAlgebra/Compactness.lean) | Compact instances under their separate assumptions |
| [`IwasawaModules/CompletedGroupAlgebra/Completeness.lean`](IwasawaModules/CompletedGroupAlgebra/Completeness.lean) | Canonical uniformities and compact-route completeness |

The [native API reference](docs/API.md), [module/instance inventory and
reproduction guide](docs/README.md) and [byte-bound manifest](docs/api-manifest.json)
describe all eleven modules at the unchanged mathematical/pinned input
`deceb449133f8bcc7fb4829e4fc167b483eef3a2`. They document 54 filtered
production named entries (including 14 instances); the production root and three
test modules export zero native entries. The tests still check source-level
clients. This is public API documentation, **not** a private-proof census,
source-coverage finding or release approval.

Import `IwasawaModules` for all public declarations or only the needed leaf:

```lean
import IwasawaModules

theorem identity_is_pseudo (R M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] :
    (LinearMap.id : M →ₗ[R] M).IsPseudoIsomorphism R :=
  LinearMap.isPseudoIsomorphism_id R
```

The aggregate root does not import the test root.
[`IwasawaModulesTests/RootAPI.lean`](IwasawaModulesTests/RootAPI.lean) tests
aggregate-only clients; [`IwasawaModulesTests/DirectAPI.lean`](IwasawaModulesTests/DirectAPI.lean)
tests leaf imports and concrete zero/nonzero finite-group examples. Both are
included through [`IwasawaModulesTests.lean`](IwasawaModulesTests.lean) in the
default build, not the production import. Implementation-private compactness
helpers are not public API.

The coefficientwise APIs need only a finite index type, not a group structure;
the tests include an empty index. The accepted development input identified above
removed the formerly unused `Group H` argument from six public declarations:
`finiteGroupAlgebraCoefficients`, `finiteGroupAlgebraTopology`,
`instTopologicalSpaceFiniteGroupAlgebra`, `finiteGroupAlgebraHomeomorph`,
`instT2SpaceFiniteGroupAlgebra` and `instCompactSpaceFiniteGroupAlgebra`, all in
`CompletedGroupAlgebra`. Ordinary calls with inferred instances retain their
meaning and definitional reduction; callers using positional `@` arguments
must remove the old group-instance argument. Multiplication and the completed
algebra results retain their group hypotheses. Two algebraic private helpers and
their private reduction lemma also omit unused coefficient-topology arguments;
topology and compactness results retain their actual hypotheses.

## Reproduce

The pinned toolchain is Lean `v4.34.0-rc2` (commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`); the sole direct library
dependency is mathlib `e37d88a26f3791ed5a93daa1f949af1021b8d103`.
[`lean-toolchain`](lean-toolchain), [`lakefile.toml`](lakefile.toml) and
[`lake-manifest.json`](lake-manifest.json) pin the entire Lake dependency graph.
Fetch its matching precompiled mathlib cache **before** building; do not
silently replace a failed cache fetch with a source rebuild:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LEAN_NUM_THREADS=2 lake --wfail build
LEAN_NUM_THREADS=2 lake --wfail build IwasawaModules IwasawaModulesTests
```

Ordinary and `-T0` downstream elaboration use `lake env lean
-DwarningAsError=true IwasawaModulesTests/RootAPI.lean` (or
`DirectAPI.lean`) and `lake env lean -T0 -DwarningAsError=true ...` after
the production `.olean` files exist. The named
tests cover actual proofs, not only type-check directives. The September 26,
2026 preparation fetched 8,892 mathlib cache objects successfully and ran a
warning-fatal default build in 15.697 seconds (2,481 reported jobs); the
warm all-eleven-module build ran in 2.275 seconds. The runtime cgroup has a
15 GiB hard memory limit. During the default invocation, sampled child-tree
RSS reached 3.70 GB and sampled *whole-cgroup* usage 14.17 GB. The author reported
a simultaneous separate doc-gen4 build; the cgroup samples include resident
cache/page memory and do not attribute usage to individual projects. These
periodic samples are **not** isolated peak requirements or portable timing
guarantees. `LEAN_NUM_THREADS=2` is a Lean runtime setting; neither
`LAKE_JOBS=2` nor `lake -Kjobs=2` is verified as a total scheduler limit for
this pinned Lake. Check local aggregate memory/process use and allow headroom.
A previous artificial 9 GB virtual-address-space ceiling made selected
checker mmap reads fail; that failure does not establish a 9 GB physical-RAM
requirement or a failing theorem. See the [native reproduction and resource
notes](docs/README.md) for details and limits.

As a separate initial downstream-use baseline on September 26, the exact README
example above elaborated warning-fatally in 2.880 seconds ordinarily and 2.892
seconds with `-T0`, after the matching cache and all project modules were built.
This used `lake env lean -j1 -DwarningAsError=true` (with `-T0` for the second
invocation), `LEAN_NUM_THREADS=1`, and a 23 GiB runtime cgroup. Periodically
sampled process-group RSS reached 3,713,712,128 and 3,747,016,704 bytes,
respectively; stdout and stderr were empty. A 300-second timeout, 18 GiB sampled
RSS watchdog and 64 GiB virtual-address-space ceiling bounded these checks.
They are observed warm-use costs, not continuous peaks, memory minima or
performance improvements over an earlier release.

## Origin and status

Beacon authored the initial nine mathematical code contributions, the
proof-preserving native-module precursor and the later lint successor that
removed unused assumptions and added no-group coefficient clients. The earlier
worker-b contribution `2e628e716ac3e6b9062adc1dd14778ae63290cbd` added
test clients, configuration, metadata, license and documentation. A distinct
worker-b Task `hive-request-5fc39d37ccb1adb18e0c62309771c4ccbe2140fa`
(UID `645fd9e7-83b8-4288-ac17-54d375560cd6`) authored the native
documentation and adapted generator/tests described in [their provenance
record](docs/README.md). Beacon subsequently clarified the lifecycle/resource
wording and added the measured README-use baseline, without changing Lean,
dependency pins or generated API data.
The original development commits begin `5e7d5c7`, `1f5ad86`,
`c6a23e5`, `e288379`, `0e71dec`, `e7a15b3`, `5e31454`, `101f3c3` and
`720331e`; the later native-module precursor is `4a1a94d`. The Lean
implementations combine **original project bridge proofs** with imported
mathlib [module support](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/RingTheory/Support.lean),
[localized-module maps](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/Algebra/Module/LocalizedModule/Submodule.lean),
[categorical ring limits](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/Algebra/Category/Ring/Limits.lean)
and [finite-algebra topology](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/Topology/Algebra/Monoid/FunOnFinite.lean)
APIs; upstream mathlib implementations are dependencies, not vendored source.
The root [LICENSE](LICENSE) matches mathlib's pinned `LICENSE` byte-for-byte
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`).
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, chapter V
motivates later Iwasawa-module work, but no book passage, proof text or source
asset is reproduced in this deliverable. Prior independent mathematical
reviews by Prism, Atlas, Lattice and Anchor addressed individual mathematical
contributions. Independent worker-a review `3010` and Beacon's ordinary
acceptance/integration of PR 11 established the exact development main input
`deceb449133f8bcc7fb4829e4fc167b483eef3a2` on September 25, 2026.
**Ordinary development acceptance is not full private/stored-body release
acceptance** and does not transfer to these subsequently authored docs.
At this documentation preparation on September 26, 2026, full assembled
proof-body, rights, resource and release checks are not certified here; any
later exact-commit independent review, acceptance and publication must be
recorded separately rather than inferred from this dated report. This is no
source-coverage decision. AI coding agents assisted the project. Git authorship
does not assert copyright ownership; contributors and reviewers have distinct
roles. Third-party adaptation and whole-artifact rights still require
independent assessment for a release.
