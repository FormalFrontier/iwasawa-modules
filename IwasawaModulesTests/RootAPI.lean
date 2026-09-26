/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import IwasawaModules

/-!
# Aggregate-root clients

These downstream examples import only the production aggregate root. They
check the generic module API and the separately parameterized topology,
separation, compactness and completeness hypotheses.
-/

set_option warningAsError true

noncomputable section

universe u v w x

namespace IwasawaModulesTests.RootAPI

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]
variable (N : Type w) [AddCommGroup N] [Module R N]
variable (P : Type x) [AddCommGroup P] [Module R P]

/-- The public predicate still reduces to its original support condition. -/
theorem nullity_definition :
    Module.IsPseudoNull R M ↔
      ∀ p : PrimeSpectrum R, p.asIdeal.height ≤ 1 →
        p ∉ Module.support R M := Iff.rfl

/-- The support definition has the stated localized-module criterion. -/
theorem nullity_localization :
    Module.IsPseudoNull R M ↔
      ∀ p : PrimeSpectrum R, p.asIdeal.height ≤ 1 →
        Subsingleton (LocalizedModule p.asIdeal.primeCompl M) :=
  Module.isPseudoNull_iff_localizedModule_subsingleton R M

/-- Submodules and quotients characterize the nullity of the middle module. -/
theorem nullity_submodule_quotient (Q : Submodule R M) :
    Module.IsPseudoNull R M ↔
      Module.IsPseudoNull R Q ∧ Module.IsPseudoNull R (M ⧸ Q) :=
  Module.isPseudoNull_iff_submodule_quotient Q

/-- The injectivity criterion localizes the actual kernel of this map. -/
theorem localized_kernel (S : Submonoid R) (f : M →ₗ[R] N) :
    Function.Injective (LocalizedModule.map S f) ↔
      Subsingleton (LocalizedModule S f.ker) :=
  LinearMap.localizedMap_injective_iff_subsingleton_localized_ker R S f

/-- The exposed predicate still reduces to its directional kernel and cokernel. -/
theorem directional_definition (f : M →ₗ[R] N) :
    f.IsPseudoIsomorphism R ↔
      Module.IsPseudoNull R f.ker ∧ Module.IsPseudoNull R (N ⧸ f.range) := Iff.rfl

/-- Pseudo-isomorphism has precisely the directional height-one test. -/
theorem directional_bijectivity (f : M →ₗ[R] N) :
    f.IsPseudoIsomorphism R ↔
      ∀ p : PrimeSpectrum R, p.asIdeal.height ≤ 1 →
        Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl f) :=
  LinearMap.isPseudoIsomorphism_iff_localizedModule_map_bijective R f

/-- Composition keeps source, intermediate and target types separate. -/
theorem directional_composition {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hf : f.IsPseudoIsomorphism R) (hg : g.IsPseudoIsomorphism R) :
    (g.comp f).IsPseudoIsomorphism R := hg.comp R hf

/-- Bijectivity supplies both directional nullity conditions. -/
theorem bijective_case (f : M →ₗ[R] N) (hf : Function.Bijective f) :
    f.IsPseudoIsomorphism R :=
  LinearMap.IsPseudoIsomorphism.of_bijective R hf

/-- The identity case needs no finiteness or domain hypotheses. -/
theorem identity_case :
    (LinearMap.id : M →ₗ[R] M).IsPseudoIsomorphism R :=
  LinearMap.isPseudoIsomorphism_id R

variable (G : ProfiniteGrp.{w})

/-- The completed ring can be formed over any commutative coefficient ring. -/
theorem ordinary_projection (U : OpenNormalSubgroup G) (a : MonoidAlgebra R G) :
    CompletedGroupAlgebra.proj R G U (CompletedGroupAlgebra.ofMonoidAlgebra R G a) =
      MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' U.toSubgroup) a :=
  CompletedGroupAlgebra.proj_ofMonoidAlgebra R G U a

/-- The quotient direction of coordinate transitions is `U ≤ V`. -/
theorem compatible_projections {U V : OpenNormalSubgroup G} (h : U ≤ V)
    (a : CompletedGroupAlgebra R G) :
    MonoidAlgebra.mapDomainRingHom R
      (QuotientGroup.map U.toSubgroup V.toSubgroup (.id _) h)
      (CompletedGroupAlgebra.proj R G U a) =
        CompletedGroupAlgebra.proj R G V a :=
  CompletedGroupAlgebra.proj_compatibility R G h a

variable [TopologicalSpace R]

/-- Coordinatewise continuity has no topological-ring or T2 prerequisite. -/
theorem coordinates_continuous {X : Type x} [TopologicalSpace X]
    (f : X → CompletedGroupAlgebra R G) :
    Continuous f ↔
      ∀ U, Continuous (CompletedGroupAlgebra.proj R G U ∘ f) :=
  CompletedGroupAlgebra.continuous_iff_proj R G f

/-- Each finite projection is continuous without topological-ring assumptions. -/
theorem projection_continuous (U : OpenNormalSubgroup G) :
    Continuous (CompletedGroupAlgebra.proj R G U) :=
  CompletedGroupAlgebra.continuous_proj R G U

variable [T2Space R]

/-- Coefficient Hausdorffness passes to the completed algebra. -/
theorem completed_separated : T2Space (CompletedGroupAlgebra R G) := inferInstance

variable (H : Type x) [Group H] [Finite H]

omit [TopologicalSpace R] [T2Space R] [Group H] in
/-- The exposed finite-level coefficient equivalence keeps its definition. -/
theorem coefficient_equiv_definition :
    CompletedGroupAlgebra.finiteGroupAlgebraCoefficients R H =
      MonoidAlgebra.coeffEquiv.trans Finsupp.equivFunOnFinite := rfl

omit [TopologicalSpace R] [T2Space R] in
/-- The coefficient equivalence also works for an arbitrary finite index type. -/
theorem coefficient_equiv_without_group (I : Type x) [Finite I] :
    CompletedGroupAlgebra.finiteGroupAlgebraCoefficients R I =
      MonoidAlgebra.coeffEquiv.trans Finsupp.equivFunOnFinite := rfl

omit [TopologicalSpace R] [T2Space R] in
/-- An empty finite index, which admits no group structure, is allowed. -/
theorem empty_index_coefficients :
    CompletedGroupAlgebra.finiteGroupAlgebraCoefficients R (Fin 0) =
      MonoidAlgebra.coeffEquiv.trans Finsupp.equivFunOnFinite := rfl

omit [T2Space R] in
/-- The empty-index homeomorphism keeps the exposed coefficient equivalence. -/
theorem empty_index_homeomorph :
    (CompletedGroupAlgebra.finiteGroupAlgebraHomeomorph R (Fin 0)).toEquiv =
      CompletedGroupAlgebra.finiteGroupAlgebraCoefficients R (Fin 0) := rfl

omit [Group H] in
/-- Finite-level separation needs only coefficient Hausdorffness. -/
theorem finite_separated : T2Space (MonoidAlgebra R H) := inferInstance

variable [CompactSpace R]

omit [T2Space R] [Group H] in
/-- Finite-level compactness does not require an `IsTopologicalRing` or T2 argument. -/
theorem finite_compact : CompactSpace (MonoidAlgebra R H) := inferInstance

variable [IsTopologicalRing R]

/-- The completed compactness route needs compact Hausdorff coefficients. -/
theorem completed_compact : CompactSpace (CompletedGroupAlgebra R G) := inferInstance

omit [T2Space R] in
/-- Finite-level completeness needs compactness but no extra T2 argument. -/
theorem finite_complete : CompleteSpace (MonoidAlgebra R H) := inferInstance

/-- Compact Hausdorff coefficient rings give completed completeness. -/
theorem completed_complete : CompleteSpace (CompletedGroupAlgebra R G) := inferInstance

omit [T2Space R] [CompactSpace R] in
/-- The named finite uniformity reduces to its old inferred instance. -/
theorem inferred_finite_uniformity : (inferInstance : UniformSpace (MonoidAlgebra R H)) =
    CompletedGroupAlgebra.finiteGroupAlgebraUniformSpace R H := rfl

omit [T2Space R] [CompactSpace R] in
/-- The named completed uniformity reduces to its old inferred instance. -/
theorem inferred_completed_uniformity : (inferInstance : UniformSpace (CompletedGroupAlgebra R G)) =
    CompletedGroupAlgebra.completedGroupAlgebraUniformSpace R G := rfl

omit [T2Space R] [CompactSpace R] in
/-- The old finite uniformity-topology coherence remains definitional. -/
theorem finite_uniformity_topology :
    (CompletedGroupAlgebra.finiteGroupAlgebraUniformSpace R H).toTopologicalSpace =
      CompletedGroupAlgebra.finiteGroupAlgebraTopology R H := rfl

omit [T2Space R] [CompactSpace R] in
/-- The old completed uniformity-topology coherence remains definitional. -/
theorem completed_uniformity_topology :
    (CompletedGroupAlgebra.completedGroupAlgebraUniformSpace R G).toTopologicalSpace =
      CompletedGroupAlgebra.inverseLimitTopology R G := rfl

end IwasawaModulesTests.RootAPI
