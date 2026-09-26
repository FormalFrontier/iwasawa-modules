# Native API reference

Fixed Lean `v4.34.0-rc2`, mathlib `e37d88a26f3791ed5a93daa1f949af1021b8d103`
and separately pinned doc-gen4 `97d4ecdfc8e09e7f511724c25e303d448de6a3db`. Full displayed signatures
retain all native implicit arguments, typeclasses and universe variables.
The eleven native module records contain **54 production named declarations**:
16 definitions (including an abbreviation), 24 theorems and 14 named instances.
The production root, two test leaves and test root each export **zero**
native named entries. The test source files still contain checked Lean clients;
zero exported native records do not mean zero source-level tests.
The filtered native tables do **not** enumerate implementation-private helpers,
local compiler declarations or stored proof bodies; this is not a private-proof
census. It does not certify axioms, proof integrity,
source coverage, rights or a release. [Reproduce and assess provenance](README.md).

Source links point only to the unchanged `.lean` files shipped here.
**Native source docstring** reproduces a matched source comment;
**Original catalogue explanation** is newly written here for an entry
without a Lean docstring. `ext_iff` is generated from `@[ext]`.

## Module and instance inventory

| Native module | Definitions | Theorems | Named instances |
| --- | ---: | ---: | ---: |
| [`IwasawaModules.PseudoIsomorphism.Basic`](../IwasawaModules/PseudoIsomorphism/Basic.lean) | 1 | 8 | 0 |
| [`IwasawaModules.PseudoIsomorphism.LinearMap`](../IwasawaModules/PseudoIsomorphism/LinearMap.lean) | 1 | 7 | 0 |
| [`IwasawaModules.CompletedGroupAlgebra.Basic`](../IwasawaModules/CompletedGroupAlgebra/Basic.lean) | 6 | 4 | 0 |
| [`IwasawaModules.CompletedGroupAlgebra.Topology`](../IwasawaModules/CompletedGroupAlgebra/Topology.lean) | 6 | 2 | 4 |
| [`IwasawaModules.CompletedGroupAlgebra.Separation`](../IwasawaModules/CompletedGroupAlgebra/Separation.lean) | 0 | 0 | 2 |
| [`IwasawaModules.CompletedGroupAlgebra.Compactness`](../IwasawaModules/CompletedGroupAlgebra/Compactness.lean) | 0 | 1 | 2 |
| [`IwasawaModules.CompletedGroupAlgebra.Completeness`](../IwasawaModules/CompletedGroupAlgebra/Completeness.lean) | 2 | 2 | 6 |
| [`IwasawaModules`](../IwasawaModules.lean) | 0 | 0 | 0 |
| [`IwasawaModulesTests.RootAPI`](../IwasawaModulesTests/RootAPI.lean) | 0 | 0 | 0 |
| [`IwasawaModulesTests.DirectAPI`](../IwasawaModulesTests/DirectAPI.lean) | 0 | 0 | 0 |
| [`IwasawaModulesTests`](../IwasawaModulesTests.lean) | 0 | 0 | 0 |

Native instance tables (name, class and type names):

- `CompletedGroupAlgebra.instTopologicalSpaceFiniteGroupAlgebra`: `TopologicalSpace` on `MonoidAlgebra`.
- `CompletedGroupAlgebra.instIsTopologicalRingFiniteGroupAlgebra`: `IsTopologicalRing` on `MonoidAlgebra`.
- `CompletedGroupAlgebra.instTopologicalSpace`: `TopologicalSpace` on `RingCat.carrier`.
- `CompletedGroupAlgebra.instIsTopologicalRing`: `IsTopologicalRing` on `RingCat.carrier`.
- `CompletedGroupAlgebra.instT2SpaceFiniteGroupAlgebra`: `T2Space` on `MonoidAlgebra`.
- `CompletedGroupAlgebra.instT2Space`: `T2Space` on `RingCat.carrier`.
- `CompletedGroupAlgebra.instCompactSpaceFiniteGroupAlgebra`: `CompactSpace` on `MonoidAlgebra`.
- `CompletedGroupAlgebra.instCompactSpace`: `CompactSpace` on `RingCat.carrier`.
- `CompletedGroupAlgebra.instUniformSpaceFiniteGroupAlgebra`: `UniformSpace` on `MonoidAlgebra`.
- `CompletedGroupAlgebra.instIsUniformAddGroupFiniteGroupAlgebra`: `IsUniformAddGroup` on `MonoidAlgebra`.
- `CompletedGroupAlgebra.instCompleteSpaceFiniteGroupAlgebra`: `CompleteSpace` on `MonoidAlgebra`.
- `CompletedGroupAlgebra.instUniformSpace`: `UniformSpace` on `RingCat.carrier`.
- `CompletedGroupAlgebra.instIsUniformAddGroup`: `IsUniformAddGroup` on `RingCat.carrier`.
- `CompletedGroupAlgebra.instCompleteSpace`: `CompleteSpace` on `RingCat.carrier`.

## Production named API

### `IwasawaModules.PseudoIsomorphism.Basic`

#### `Module.IsPseudoNull`

Kind: `def`.

```lean
def Module.IsPseudoNull (R : Type u_1) (M : Type u_2) [CommRing R] [AddCommGroup M] [Module R M] : Prop
```

**Native source docstring:** A module is pseudo-null when it vanishes after localization at every prime
of height at most one. Finiteness hypotheses belong on structure theorems, not
on this predicate.

[Source](../IwasawaModules/PseudoIsomorphism/Basic.lean#L27) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `Module.isPseudoNull_iff_localizedModule_subsingleton`

Kind: `theorem`.

```lean
theorem Module.isPseudoNull_iff_localizedModule_subsingleton (R : Type u_1) (M : Type u_2) [CommRing R] [AddCommGroup M] [Module R M] : IsPseudoNull R M ↔ ∀ (p : PrimeSpectrum R), p.asIdeal.height ≤ 1 → Subsingleton (LocalizedModule p.asIdeal.primeCompl M)
```

**Native source docstring:** Pseudo-nullity restated directly in terms of localized modules.

[Source](../IwasawaModules/PseudoIsomorphism/Basic.lean#L33) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `Module.IsPseudoNull.of_subsingleton`

Kind: `theorem`.

```lean
theorem Module.IsPseudoNull.of_subsingleton (R : Type u_1) (M : Type u_2) [CommRing R] [AddCommGroup M] [Module R M] [Subsingleton M] : IsPseudoNull R M
```

**Native source docstring:** Every subsingleton module is pseudo-null.

[Source](../IwasawaModules/PseudoIsomorphism/Basic.lean#L40) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `Module.IsPseudoNull.of_injective`

Kind: `theorem`.

```lean
theorem Module.IsPseudoNull.of_injective {R : Type u_1} {M : Type u_2} [CommRing R] [AddCommGroup M] [Module R M] {N : Type u_3} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (hf : Function.Injective ⇑f) (hN : IsPseudoNull R N) : IsPseudoNull R M
```

**Native source docstring:** A submodule of a pseudo-null module is pseudo-null, expressed for an
arbitrary injective linear map.

[Source](../IwasawaModules/PseudoIsomorphism/Basic.lean#L50) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `Module.IsPseudoNull.of_surjective`

Kind: `theorem`.

```lean
theorem Module.IsPseudoNull.of_surjective {R : Type u_1} {M : Type u_2} [CommRing R] [AddCommGroup M] [Module R M] {N : Type u_3} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (hf : Function.Surjective ⇑f) (hM : IsPseudoNull R M) : IsPseudoNull R N
```

**Native source docstring:** A quotient of a pseudo-null module is pseudo-null, expressed for an
arbitrary surjective linear map.

[Source](../IwasawaModules/PseudoIsomorphism/Basic.lean#L57) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `Module.IsPseudoNull.of_exact`

Kind: `theorem`.

```lean
theorem Module.IsPseudoNull.of_exact {R : Type u_1} {M : Type u_2} [CommRing R] [AddCommGroup M] [Module R M] {N : Type u_3} {P : Type u_4} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : Function.Exact ⇑f ⇑g) (hf : Function.Injective ⇑f) (hg : Function.Surjective ⇑g) (hM : IsPseudoNull R M) (hP : IsPseudoNull R P) : IsPseudoNull R N
```

**Native source docstring:** Pseudo-null modules are closed under extensions.

[Source](../IwasawaModules/PseudoIsomorphism/Basic.lean#L64) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `Module.isPseudoNull_iff_of_exact`

Kind: `theorem`.

```lean
theorem Module.isPseudoNull_iff_of_exact {R : Type u_1} {M : Type u_2} [CommRing R] [AddCommGroup M] [Module R M] {N : Type u_3} {P : Type u_4} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : Function.Exact ⇑f ⇑g) (hf : Function.Injective ⇑f) (hg : Function.Surjective ⇑g) : IsPseudoNull R N ↔ IsPseudoNull R M ∧ IsPseudoNull R P
```

**Native source docstring:** In a short exact sequence, the middle module is pseudo-null exactly when
both outer modules are pseudo-null.

[Source](../IwasawaModules/PseudoIsomorphism/Basic.lean#L73) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `Module.isPseudoNull_iff_submodule_quotient`

Kind: `theorem`.

```lean
theorem Module.isPseudoNull_iff_submodule_quotient {R : Type u_1} {M : Type u_2} [CommRing R] [AddCommGroup M] [Module R M] (Q : Submodule R M) : IsPseudoNull R M ↔ IsPseudoNull R ↥Q ∧ IsPseudoNull R (M ⧸ Q)
```

**Native source docstring:** A module is pseudo-null exactly when a submodule and the corresponding
quotient are both pseudo-null.

[Source](../IwasawaModules/PseudoIsomorphism/Basic.lean#L83) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `LinearEquiv.isPseudoNull_iff`

Kind: `theorem`.

```lean
theorem LinearEquiv.isPseudoNull_iff {R : Type u} {M : Type v} {N : Type w} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) : Module.IsPseudoNull R M ↔ Module.IsPseudoNull R N
```

**Native source docstring:** Pseudo-nullity is invariant under a linear equivalence.

[Source](../IwasawaModules/PseudoIsomorphism/Basic.lean#L100) (native source start line; generated `ext_iff` points to `@[ext]`).

### `IwasawaModules.PseudoIsomorphism.LinearMap`

#### `LinearMap.IsPseudoIsomorphism`

Kind: `def`.

```lean
def LinearMap.IsPseudoIsomorphism (R : Type u) [CommRing R] {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) : Prop
```

**Native source docstring:** A linear map is a pseudo-isomorphism when its kernel and cokernel are
pseudo-null. This is directional data, not an equivalence between modules.

[Source](../IwasawaModules/PseudoIsomorphism/LinearMap.lean#L31) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `LinearMap.localizedMap_injective_iff_subsingleton_localized_ker`

Kind: `theorem`.

```lean
theorem LinearMap.localizedMap_injective_iff_subsingleton_localized_ker (R : Type u) [CommRing R] {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (S : Submonoid R) (f : M →ₗ[R] N) : Function.Injective ⇑((LocalizedModule.map S) f) ↔ Subsingleton (LocalizedModule S ↥f.ker)
```

**Native source docstring:** Localization of a linear map is injective exactly when the localization of
its kernel is trivial.

[Source](../IwasawaModules/PseudoIsomorphism/LinearMap.lean#L36) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `LinearMap.isPseudoIsomorphism_iff_localizedModule_subsingleton`

Kind: `theorem`.

```lean
theorem LinearMap.isPseudoIsomorphism_iff_localizedModule_subsingleton (R : Type u) [CommRing R] {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) : IsPseudoIsomorphism R f ↔ (∀ (p : PrimeSpectrum R), p.asIdeal.height ≤ 1 → Subsingleton (LocalizedModule p.asIdeal.primeCompl ↥f.ker)) ∧ ∀ (p : PrimeSpectrum R), p.asIdeal.height ≤ 1 → Subsingleton (LocalizedModule p.asIdeal.primeCompl (N ⧸ f.range))
```

**Native source docstring:** The definition restated pointwise using localized kernels and cokernels.

[Source](../IwasawaModules/PseudoIsomorphism/LinearMap.lean#L55) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `LinearMap.isPseudoIsomorphism_iff_localizedModule_map_bijective`

Kind: `theorem`.

```lean
theorem LinearMap.isPseudoIsomorphism_iff_localizedModule_map_bijective (R : Type u) [CommRing R] {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) : IsPseudoIsomorphism R f ↔ ∀ (p : PrimeSpectrum R), p.asIdeal.height ≤ 1 → Function.Bijective ⇑((LocalizedModule.map p.asIdeal.primeCompl) f)
```

**Native source docstring:** A linear map is a pseudo-isomorphism exactly when it becomes bijective at
every prime of height at most one.

[Source](../IwasawaModules/PseudoIsomorphism/LinearMap.lean#L65) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `LinearMap.IsPseudoIsomorphism.of_bijective`

Kind: `theorem`.

```lean
theorem LinearMap.IsPseudoIsomorphism.of_bijective (R : Type u) [CommRing R] {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {f : M →ₗ[R] N} (hf : Function.Bijective ⇑f) : IsPseudoIsomorphism R f
```

**Native source docstring:** Every bijective linear map is a pseudo-isomorphism.

[Source](../IwasawaModules/PseudoIsomorphism/LinearMap.lean#L91) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `LinearMap.isPseudoIsomorphism_id`

Kind: `theorem`.

```lean
theorem LinearMap.isPseudoIsomorphism_id (R : Type u) [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] : IsPseudoIsomorphism R id
```

**Native source docstring:** The identity linear map is a pseudo-isomorphism.

[Source](../IwasawaModules/PseudoIsomorphism/LinearMap.lean#L100) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `LinearMap.IsPseudoIsomorphism.comp`

Kind: `theorem`.

```lean
theorem LinearMap.IsPseudoIsomorphism.comp (R : Type u) [CommRing R] {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {P : Type u_1} [AddCommGroup P] [Module R P] {g : N →ₗ[R] P} {f : M →ₗ[R] N} (hg : IsPseudoIsomorphism R g) (hf : IsPseudoIsomorphism R f) : IsPseudoIsomorphism R (g ∘ₗ f)
```

**Native source docstring:** The composite of two pseudo-isomorphisms is a pseudo-isomorphism.

[Source](../IwasawaModules/PseudoIsomorphism/LinearMap.lean#L105) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `LinearEquiv.isPseudoIsomorphism`

Kind: `theorem`.

```lean
theorem LinearEquiv.isPseudoIsomorphism (R : Type u) [CommRing R] {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) : LinearMap.IsPseudoIsomorphism R ↑e
```

**Native source docstring:** The linear map underlying a linear equivalence is a pseudo-isomorphism.

[Source](../IwasawaModules/PseudoIsomorphism/LinearMap.lean#L134) (native source start line; generated `ext_iff` points to `@[ext]`).

### `IwasawaModules.CompletedGroupAlgebra.Basic`

#### `CompletedGroupAlgebra.monoidAlgebraFunctor`

Kind: `def`.

```lean
noncomputable def CompletedGroupAlgebra.monoidAlgebraFunctor (R : Type u) [CommRing R] : CategoryTheory.Functor MonCat RingCat
```

**Native source docstring:** Ordinary monoid algebras over `R`, functorial in arbitrary monoids.

The codomain is `RingCat`, rather than `CommRingCat`, because the monoids and
their monoid algebras need not be commutative.

[Source](../IwasawaModules/CompletedGroupAlgebra/Basic.lean#L34) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.finiteQuotientSystem`

Kind: `def`.

```lean
noncomputable def CompletedGroupAlgebra.finiteQuotientSystem (R : Type u) [CommRing R] (G : ProfiniteGrp.{v}) : CategoryTheory.Functor (OpenNormalSubgroup ↑G.toProfinite.toTop) RingCat
```

**Native source docstring:** The inverse system `U ↦ R[G/U]` over the open normal subgroups of a
profinite group `G`.

[Source](../IwasawaModules/CompletedGroupAlgebra/Basic.lean#L46) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra`

Kind: `def`.

```lean
noncomputable abbrev CompletedGroupAlgebra (R : Type u) [CommRing R] (G : ProfiniteGrp.{v}) : RingCat
```

**Native source docstring:** The underlying ring of the inverse limit of `R[G/U]` over all open normal
subgroups `U` of `G`.

The topology is asserted separately in
`IwasawaModules.CompletedGroupAlgebra.Topology`.

[Source](../IwasawaModules/CompletedGroupAlgebra/Basic.lean#L55) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.proj`

Kind: `def`.

```lean
noncomputable def CompletedGroupAlgebra.proj (R : Type u) [CommRing R] (G : ProfiniteGrp.{v}) (U : OpenNormalSubgroup ↑G.toProfinite.toTop) : ↑(CompletedGroupAlgebra R G) →+* MonoidAlgebra R (↑G.toProfinite.toTop ⧸ ↑U.toOpenSubgroup)
```

**Native source docstring:** Projection from the finite-quotient group-algebra limit to one coordinate
`R[G/U]`.

[Source](../IwasawaModules/CompletedGroupAlgebra/Basic.lean#L63) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.ext`

Kind: `theorem`.

```lean
theorem CompletedGroupAlgebra.ext (R : Type u) [CommRing R] (G : ProfiniteGrp.{v}) (x y : ↑(CompletedGroupAlgebra R G)) (h : ∀ (U : OpenNormalSubgroup ↑G.toProfinite.toTop), (proj R G U) x = (proj R G U) y) : x = y
```

**Native source docstring:** Two elements of a finite-quotient group-algebra limit are equal when all
their finite-quotient coordinates are equal.

[Source](../IwasawaModules/CompletedGroupAlgebra/Basic.lean#L69) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.ext_iff`

Kind: `theorem`.

```lean
theorem CompletedGroupAlgebra.ext_iff {R : Type u} [CommRing R] {G : ProfiniteGrp.{v}} {x y : ↑(CompletedGroupAlgebra R G)} : x = y ↔ ∀ (U : OpenNormalSubgroup ↑G.toProfinite.toTop), (proj R G U) x = (proj R G U) y
```

**Original catalogue explanation (not a Lean docstring):** The `@[ext]`-generated equivalence says that completed elements agree exactly when all their finite-quotient projections agree; its source is the preceding `ext` theorem.

[Source](../IwasawaModules/CompletedGroupAlgebra/Basic.lean#L71) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.ordinaryCone`

Kind: `def`.

```lean
noncomputable def CompletedGroupAlgebra.ordinaryCone (R : Type u) [CommRing R] (G : ProfiniteGrp.{v}) : CategoryTheory.Limits.Cone (finiteQuotientSystem R G)
```

**Native source docstring:** The ordinary group algebra `R[G]` maps compatibly to all finite-quotient
group algebras.

[Source](../IwasawaModules/CompletedGroupAlgebra/Basic.lean#L77) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.ofMonoidAlgebra`

Kind: `def`.

```lean
noncomputable def CompletedGroupAlgebra.ofMonoidAlgebra (R : Type u) [CommRing R] (G : ProfiniteGrp.{v}) : MonoidAlgebra R ↑G.toProfinite.toTop →+* ↑(CompletedGroupAlgebra R G)
```

**Native source docstring:** The canonical ring homomorphism from the ordinary group algebra to its
finite-quotient inverse limit.

[Source](../IwasawaModules/CompletedGroupAlgebra/Basic.lean#L96) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.proj_ofMonoidAlgebra`

Kind: `theorem`.

```lean
theorem CompletedGroupAlgebra.proj_ofMonoidAlgebra (R : Type u) [CommRing R] (G : ProfiniteGrp.{v}) (U : OpenNormalSubgroup ↑G.toProfinite.toTop) (x : MonoidAlgebra R ↑G.toProfinite.toTop) : (proj R G U) ((ofMonoidAlgebra R G) x) = (MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' ↑U.toOpenSubgroup)) x
```

**Original catalogue explanation (not a Lean docstring):** The ordinary-to-completed homomorphism reduces at each finite quotient to the group-algebra map induced by the quotient homomorphism.

[Source](../IwasawaModules/CompletedGroupAlgebra/Basic.lean#L102) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.proj_compatibility`

Kind: `theorem`.

```lean
theorem CompletedGroupAlgebra.proj_compatibility (R : Type u) [CommRing R] (G : ProfiniteGrp.{v}) {U V : OpenNormalSubgroup ↑G.toProfinite.toTop} (h : U ≤ V) (x : ↑(CompletedGroupAlgebra R G)) : (MonoidAlgebra.mapDomainRingHom R (QuotientGroup.map (↑U.toOpenSubgroup) (↑V.toOpenSubgroup) (MonoidHom.id ↑G.toProfinite.toTop) h)) ((proj R G U) x) = (proj R G V) x
```

**Native source docstring:** The coordinate projections satisfy the expected quotient compatibility.

[Source](../IwasawaModules/CompletedGroupAlgebra/Basic.lean#L110) (native source start line; generated `ext_iff` points to `@[ext]`).

### `IwasawaModules.CompletedGroupAlgebra.Topology`

#### `CompletedGroupAlgebra.finiteGroupAlgebraCoefficients`

Kind: `def`.

```lean
noncomputable def CompletedGroupAlgebra.finiteGroupAlgebraCoefficients (R : Type u) [CommRing R] (H : Type v) [Finite H] : MonoidAlgebra R H ≃ (H → R)
```

**Native source docstring:** For a finite index type `H`, the underlying coefficient space of its
monoid algebra is equivalent to `H → R`; no group structure on `H` is needed.

[Source](../IwasawaModules/CompletedGroupAlgebra/Topology.lean#L39) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.finiteGroupAlgebraTopology`

Kind: `def`.

```lean
noncomputable def CompletedGroupAlgebra.finiteGroupAlgebraTopology (R : Type u) [CommRing R] [TopologicalSpace R] (H : Type v) [Finite H] : TopologicalSpace (MonoidAlgebra R H)
```

**Native source docstring:** The coefficientwise product topology for a finite index type.

[Source](../IwasawaModules/CompletedGroupAlgebra/Topology.lean#L45) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.instTopologicalSpaceFiniteGroupAlgebra`

Kind: `instance`.

```lean
noncomputable instance CompletedGroupAlgebra.instTopologicalSpaceFiniteGroupAlgebra (R : Type u) [CommRing R] [TopologicalSpace R] (H : Type v) [Finite H] : TopologicalSpace (MonoidAlgebra R H)
```

**Native source docstring:** The coefficientwise product topology on a finite-index coefficient space.

[Source](../IwasawaModules/CompletedGroupAlgebra/Topology.lean#L51) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.finiteGroupAlgebraHomeomorph`

Kind: `def`.

```lean
noncomputable def CompletedGroupAlgebra.finiteGroupAlgebraHomeomorph (R : Type u) [CommRing R] [TopologicalSpace R] (H : Type v) [Finite H] : MonoidAlgebra R H ≃ₜ (H → R)
```

**Native source docstring:** A finite-index coefficient space with its topology is homeomorphic
to the finite product of copies of its coefficient ring.

[Source](../IwasawaModules/CompletedGroupAlgebra/Topology.lean#L57) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.finiteGroupAlgebraRingTopology`

Kind: `def`.

```lean
noncomputable def CompletedGroupAlgebra.finiteGroupAlgebraRingTopology (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (H : Type v) [Group H] [Finite H] : RingTopology (MonoidAlgebra R H)
```

**Native source docstring:** The coefficientwise product ring topology on the group algebra of a finite
group.

[Source](../IwasawaModules/CompletedGroupAlgebra/Topology.lean#L69) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.instIsTopologicalRingFiniteGroupAlgebra`

Kind: `instance`.

```lean
instance CompletedGroupAlgebra.instIsTopologicalRingFiniteGroupAlgebra (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (H : Type v) [Group H] [Finite H] : IsTopologicalRing (MonoidAlgebra R H)
```

**Native source docstring:** A finite group algebra is a topological ring for the coefficientwise
product topology.

[Source](../IwasawaModules/CompletedGroupAlgebra/Topology.lean#L118) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.inverseLimitTopology`

Kind: `def`.

```lean
noncomputable def CompletedGroupAlgebra.inverseLimitTopology (R : Type u) [CommRing R] [TopologicalSpace R] (G : ProfiniteGrp.{v}) : TopologicalSpace ↑(CompletedGroupAlgebra R G)
```

**Native source docstring:** The inverse-limit topology on a completed group algebra, induced by all
finite-quotient projections.

[Source](../IwasawaModules/CompletedGroupAlgebra/Topology.lean#L125) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.ringTopology`

Kind: `def`.

```lean
noncomputable def CompletedGroupAlgebra.ringTopology (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (G : ProfiniteGrp.{v}) : RingTopology ↑(CompletedGroupAlgebra R G)
```

**Native source docstring:** The ring topology underlying the inverse-limit topology on a completed
group algebra.

[Source](../IwasawaModules/CompletedGroupAlgebra/Topology.lean#L133) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.instTopologicalSpace`

Kind: `instance`.

```lean
noncomputable instance CompletedGroupAlgebra.instTopologicalSpace (R : Type u) [CommRing R] [TopologicalSpace R] (G : ProfiniteGrp.{v}) : TopologicalSpace ↑(CompletedGroupAlgebra R G)
```

**Native source docstring:** The inverse-limit topology on a completed group algebra.

[Source](../IwasawaModules/CompletedGroupAlgebra/Topology.lean#L201) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.instIsTopologicalRing`

Kind: `instance`.

```lean
instance CompletedGroupAlgebra.instIsTopologicalRing (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (G : ProfiniteGrp.{v}) : IsTopologicalRing ↑(CompletedGroupAlgebra R G)
```

**Native source docstring:** A completed group algebra is a topological ring for its inverse-limit
topology.

[Source](../IwasawaModules/CompletedGroupAlgebra/Topology.lean#L206) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.continuous_proj`

Kind: `theorem`.

```lean
theorem CompletedGroupAlgebra.continuous_proj (R : Type u) [CommRing R] [TopologicalSpace R] (G : ProfiniteGrp.{v}) (U : OpenNormalSubgroup ↑G.toProfinite.toTop) : Continuous ⇑(proj R G U)
```

**Native source docstring:** Every finite-quotient projection from a completed group algebra is
continuous.

[Source](../IwasawaModules/CompletedGroupAlgebra/Topology.lean#L213) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.continuous_iff_proj`

Kind: `theorem`.

```lean
theorem CompletedGroupAlgebra.continuous_iff_proj {X : Type u_1} [TopologicalSpace X] (R : Type u) [CommRing R] [TopologicalSpace R] (G : ProfiniteGrp.{v}) (f : X → ↑(CompletedGroupAlgebra R G)) : Continuous f ↔ ∀ (U : OpenNormalSubgroup ↑G.toProfinite.toTop), Continuous (⇑(proj R G U) ∘ f)
```

**Native source docstring:** A map to a completed group algebra is continuous if and only if all of its
finite-quotient coordinates are continuous.

[Source](../IwasawaModules/CompletedGroupAlgebra/Topology.lean#L222) (native source start line; generated `ext_iff` points to `@[ext]`).

### `IwasawaModules.CompletedGroupAlgebra.Separation`

#### `CompletedGroupAlgebra.instT2SpaceFiniteGroupAlgebra`

Kind: `instance`.

```lean
instance CompletedGroupAlgebra.instT2SpaceFiniteGroupAlgebra (R : Type u) [CommRing R] [TopologicalSpace R] [T2Space R] (H : Type v) [Finite H] : T2Space (MonoidAlgebra R H)
```

**Native source docstring:** A finite-index coefficient space is Hausdorff when
its coefficient ring is Hausdorff.

[Source](../IwasawaModules/CompletedGroupAlgebra/Separation.lean#L31) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.instT2Space`

Kind: `instance`.

```lean
instance CompletedGroupAlgebra.instT2Space (R : Type u) [CommRing R] [TopologicalSpace R] [T2Space R] (G : ProfiniteGrp.{v}) : T2Space ↑(CompletedGroupAlgebra R G)
```

**Native source docstring:** A completed group algebra with its inverse-limit topology is Hausdorff
when its coefficient ring is Hausdorff.

[Source](../IwasawaModules/CompletedGroupAlgebra/Separation.lean#L38) (native source start line; generated `ext_iff` points to `@[ext]`).

### `IwasawaModules.CompletedGroupAlgebra.Compactness`

#### `CompletedGroupAlgebra.continuous_mapDomainRingHom`

Kind: `theorem`.

```lean
theorem CompletedGroupAlgebra.continuous_mapDomainRingHom (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {H : Type v} {K : Type w} [Group H] [Finite H] [Group K] [Finite K] (f : H →* K) : Continuous ⇑(MonoidAlgebra.mapDomainRingHom R f)
```

**Native source docstring:** Mapping the group variable of a finite group algebra is continuous for
the coefficientwise topologies.

[Source](../IwasawaModules/CompletedGroupAlgebra/Compactness.lean#L35) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.instCompactSpaceFiniteGroupAlgebra`

Kind: `instance`.

```lean
instance CompletedGroupAlgebra.instCompactSpaceFiniteGroupAlgebra (R : Type u) [CommRing R] [TopologicalSpace R] [CompactSpace R] (H : Type v) [Finite H] : CompactSpace (MonoidAlgebra R H)
```

**Native source docstring:** A finite-index coefficient space is compact when
its coefficient ring is compact.

[Source](../IwasawaModules/CompletedGroupAlgebra/Compactness.lean#L70) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.instCompactSpace`

Kind: `instance`.

```lean
instance CompletedGroupAlgebra.instCompactSpace (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R] (G : ProfiniteGrp.{v}) : CompactSpace ↑(CompletedGroupAlgebra R G)
```

**Native source docstring:** A completed group algebra with its inverse-limit topology is compact when
its coefficient ring is compact and Hausdorff.

[Source](../IwasawaModules/CompletedGroupAlgebra/Compactness.lean#L174) (native source start line; generated `ext_iff` points to `@[ext]`).

### `IwasawaModules.CompletedGroupAlgebra.Completeness`

#### `CompletedGroupAlgebra.finiteGroupAlgebraUniformSpace`

Kind: `def`.

```lean
noncomputable def CompletedGroupAlgebra.finiteGroupAlgebraUniformSpace (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (H : Type v) [Group H] [Finite H] : UniformSpace (MonoidAlgebra R H)
```

**Native source docstring:** The canonical additive-group uniformity on a finite group algebra with its
coefficientwise topology.

[Source](../IwasawaModules/CompletedGroupAlgebra/Completeness.lean#L33) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.finiteGroupAlgebraUniformSpace_toTopologicalSpace`

Kind: `theorem`.

```lean
theorem CompletedGroupAlgebra.finiteGroupAlgebraUniformSpace_toTopologicalSpace (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (H : Type v) [Group H] [Finite H] : (finiteGroupAlgebraUniformSpace R H).toTopologicalSpace = finiteGroupAlgebraTopology R H
```

**Native source docstring:** The canonical uniformity induces the existing coefficientwise topology.

[Source](../IwasawaModules/CompletedGroupAlgebra/Completeness.lean#L41) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.instUniformSpaceFiniteGroupAlgebra`

Kind: `instance`.

```lean
noncomputable instance CompletedGroupAlgebra.instUniformSpaceFiniteGroupAlgebra (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (H : Type v) [Group H] [Finite H] : UniformSpace (MonoidAlgebra R H)
```

**Native source docstring:** The canonical additive-group uniformity on a finite group algebra.

[Source](../IwasawaModules/CompletedGroupAlgebra/Completeness.lean#L49) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.instIsUniformAddGroupFiniteGroupAlgebra`

Kind: `instance`.

```lean
instance CompletedGroupAlgebra.instIsUniformAddGroupFiniteGroupAlgebra (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (H : Type v) [Group H] [Finite H] : IsUniformAddGroup (MonoidAlgebra R H)
```

**Native source docstring:** A finite group algebra is a uniform additive group for its canonical
additive-group uniformity.

[Source](../IwasawaModules/CompletedGroupAlgebra/Completeness.lean#L55) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.instCompleteSpaceFiniteGroupAlgebra`

Kind: `instance`.

```lean
instance CompletedGroupAlgebra.instCompleteSpaceFiniteGroupAlgebra (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] (H : Type v) [Group H] [Finite H] : CompleteSpace (MonoidAlgebra R H)
```

**Native source docstring:** A compact finite group algebra is complete for its canonical
additive-group uniformity.

[Source](../IwasawaModules/CompletedGroupAlgebra/Completeness.lean#L62) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.completedGroupAlgebraUniformSpace`

Kind: `def`.

```lean
noncomputable def CompletedGroupAlgebra.completedGroupAlgebraUniformSpace (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (G : ProfiniteGrp.{v}) : UniformSpace ↑(CompletedGroupAlgebra R G)
```

**Native source docstring:** The canonical additive-group uniformity on a completed group algebra with
its inverse-limit topology.

[Source](../IwasawaModules/CompletedGroupAlgebra/Completeness.lean#L69) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.completedGroupAlgebraUniformSpace_toTopologicalSpace`

Kind: `theorem`.

```lean
theorem CompletedGroupAlgebra.completedGroupAlgebraUniformSpace_toTopologicalSpace (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (G : ProfiniteGrp.{v}) : (completedGroupAlgebraUniformSpace R G).toTopologicalSpace = inverseLimitTopology R G
```

**Native source docstring:** The canonical uniformity induces the existing inverse-limit topology.

[Source](../IwasawaModules/CompletedGroupAlgebra/Completeness.lean#L77) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.instUniformSpace`

Kind: `instance`.

```lean
noncomputable instance CompletedGroupAlgebra.instUniformSpace (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (G : ProfiniteGrp.{v}) : UniformSpace ↑(CompletedGroupAlgebra R G)
```

**Native source docstring:** The canonical additive-group uniformity on a completed group algebra.

[Source](../IwasawaModules/CompletedGroupAlgebra/Completeness.lean#L85) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.instIsUniformAddGroup`

Kind: `instance`.

```lean
instance CompletedGroupAlgebra.instIsUniformAddGroup (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (G : ProfiniteGrp.{v}) : IsUniformAddGroup ↑(CompletedGroupAlgebra R G)
```

**Native source docstring:** A completed group algebra is a uniform additive group for its canonical
additive-group uniformity.

[Source](../IwasawaModules/CompletedGroupAlgebra/Completeness.lean#L91) (native source start line; generated `ext_iff` points to `@[ext]`).

#### `CompletedGroupAlgebra.instCompleteSpace`

Kind: `instance`.

```lean
instance CompletedGroupAlgebra.instCompleteSpace (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R] (G : ProfiniteGrp.{v}) : CompleteSpace ↑(CompletedGroupAlgebra R G)
```

**Native source docstring:** A completed group algebra over a compact Hausdorff coefficient ring is
complete for its canonical additive-group uniformity.

[Source](../IwasawaModules/CompletedGroupAlgebra/Completeness.lean#L98) (native source start line; generated `ext_iff` points to `@[ext]`).

### `IwasawaModules`

Zero native named entries; this module reexports the production leaves.

## Checked-use modules (zero exported native entries)

The [aggregate-root tests](../IwasawaModulesTests/RootAPI.lean) and
[direct-leaf tests](../IwasawaModulesTests/DirectAPI.lean) elaborate named
clients, including zero and nonzero coefficients, a noncommutative finite
group and an empty finite index. Their native records export zero named
declarations and zero instances. The [test root](../IwasawaModulesTests.lean)
also has zero native entries and imports both leaves; these test clients
are checked by the default Lake build, not exported through the
production aggregate root.
