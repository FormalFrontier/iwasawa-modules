# Iwasawa modules

Reusable Lean foundations for pseudo-null modules, directional
pseudo-isomorphisms and finite-quotient completed group algebras. **Authors:
Formal Frontier Agents. License: Apache-2.0.** See [LICENSE](LICENSE).

## Headline results

- **Pseudo-nullity and short exact sequences.** Over any commutative ring,
  [`Module.IsPseudoNull`](IwasawaModules/PseudoIsomorphism/Basic.lean#L30)
  says a module's support avoids primes of height at most one; equivalently,
  [each such localization vanishes](IwasawaModules/PseudoIsomorphism/Basic.lean#L34).
  Submodules, quotients and extensions preserve pseudo-nullity, and in a short
  exact sequence the middle term is pseudo-null exactly when both endpoints
  are ([exact-sequence criterion](IwasawaModules/PseudoIsomorphism/Basic.lean#L75)).
  The predicate needs no finite-generation, Noetherianity or domain hypothesis.
- **Directional map calculus.** A *specified* linear map has pseudo-null kernel
  and cokernel exactly when it is [bijective after localization](IwasawaModules/PseudoIsomorphism/LinearMap.lean#L67)
  at every prime of height at most one. Identity and bijective maps qualify;
  [composition](IwasawaModules/PseudoIsomorphism/LinearMap.lean#L106) preserves
  the predicate, with independent scalar and module universes. This gives no
  unrestricted reverse arrow or symmetric relation.
- **Completed group algebra.** For a commutative coefficient ring `R` and a
  profinite group `G`, [`CompletedGroupAlgebra R G`](IwasawaModules/CompletedGroupAlgebra/Basic.lean#L60)
  is the finite-quotient group-algebra limit in `RingCat`, so `G` need not be
  commutative. Its [coordinate projections](IwasawaModules/CompletedGroupAlgebra/Basic.lean#L65)
  are compatible and detect equality; the [canonical ring map](IwasawaModules/CompletedGroupAlgebra/Basic.lean#L98)
  from `R[G]` has a [coordinate formula](IwasawaModules/CompletedGroupAlgebra/Basic.lean#L103).
  No injectivity or density of this map is asserted.
- **Coefficientwise topology and separation.** For any finite index type,
  even an empty one, [coefficient extraction is a homeomorphism](IwasawaModules/CompletedGroupAlgebra/Topology.lean#L59)
  with a finite product; this part needs no group structure. The completed
  topology is induced by finite-quotient projections: a map into the completion
  is [continuous iff each coordinate is](IwasawaModules/CompletedGroupAlgebra/Topology.lean#L224).
  Hausdorff coefficients give [finite-level](IwasawaModules/CompletedGroupAlgebra/Separation.lean#L33)
  and [completed](IwasawaModules/CompletedGroupAlgebra/Separation.lean#L40)
  Hausdorff spaces. Multiplicative/topological-ring results retain their group
  and ring-continuity hypotheses.
- **Compact-route completeness.** [Finite-index coefficient spaces](IwasawaModules/CompletedGroupAlgebra/Compactness.lean#L72)
  are compact over compact coefficients *without* a Hausdorff or topological-ring
  assumption. [Finite-level completeness](IwasawaModules/CompletedGroupAlgebra/Completeness.lean#L64)
  for canonical additive-group uniformity additionally needs a topological ring.
  [Completed compactness](IwasawaModules/CompletedGroupAlgebra/Compactness.lean#L176)
  and [completed completeness](IwasawaModules/CompletedGroupAlgebra/Completeness.lean#L100)
  by this route need compact **and Hausdorff** topological-ring coefficients;
  merely complete coefficients are not covered.

These noncomputable constructions also include the zero coefficient ring.
Compact-module structure, `Z_p[[Gamma]]` comparisons, Iwasawa structure and
invariants, growth, adjoints and full source coverage remain outside this library.
The [native API reference](docs/API.md) gives signatures and further declarations.

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
clients. This public API catalogue is **not** a private-proof census or a
source-coverage finding; exact release review and proof-audit evidence are
recorded separately.

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
the tests include an empty index. Six public declarations no longer take a
formerly unused `Group H` argument:
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
```

The default build includes `IwasawaModules` and `IwasawaModulesTests`; a second
explicit-target build is optional. Direct ordinary or `-T0` elaboration of the
test leaves is also an optional diagnostic, not an additional release gate. The
tests prove their client statements, rather than only checking types. Historical
build and warm-client timing, resource bounds and native extraction details are
in the [reproduction guide](docs/README.md); none is a current memory minimum.

## Provenance and release status

Beacon contributed the original mathematical Lean bridges, proof-preserving
native-module adaptation, lint cleanup and no-group coefficient clients, as well
as later documentation and usage measurements. Separate Formal Frontier
contributors supplied public test clients, configuration, metadata and initial
documentation, and the native API catalogue, adapted generator and its tests.
Prism, Atlas, Lattice and Anchor independently reviewed individual historical
mathematical contributions; later development and initial-release candidates
also received independent review. AI agents assisted authoring and review.
The Lean implementations combine **original project bridge proofs** with imported
mathlib [module support](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/RingTheory/Support.lean),
[localized-module maps](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/Algebra/Module/LocalizedModule/Submodule.lean),
[categorical ring limits](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/Algebra/Category/Ring/Limits.lean)
and [finite-algebra topology](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/Topology/Algebra/Monoid/FunOnFinite.lean)
APIs; upstream mathlib implementations are dependencies, not vendored source.
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields* (corrected second
edition, May 2020), Chapter V §§1, 3, 5, motivates a wider theory only; no
book text, proof or asset is included or claimed formalized.

The original public snapshot and a later CI-maintenance successor have been
independently reviewed and published. The exact release record governs each
published commit, transitive standard-axiom audit (including private/generated
declarations), rights decision and mirror verification; this README does not
approve a new candidate or decide source coverage. The [LICENSE](LICENSE) and
collective author credit do not assert an invented copyright holder. The native
adapter's [public lineage and rights notes](docs/README.md#expression-origins-and-rights)
distinguish imported and adapted contributions.
