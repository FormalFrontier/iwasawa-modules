/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import IwasawaModules.CompletedGroupAlgebra.Separation
public import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compactness of completed group algebras

This file proves that the coefficientwise topology on a finite group algebra
and the inverse-limit topology on a completed group algebra are compact when
the coefficient ring is compact and Hausdorff.

The Hausdorff hypothesis ensures that the compatibility equations defining
the inverse limit cut out a closed subset of the product of the finite-level
group algebras. No completeness or density assertion is made.
-/

public section

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Topology

universe u v w

namespace CompletedGroupAlgebra

/-- Mapping the group variable of a finite group algebra is continuous for
the coefficientwise topologies. -/
theorem continuous_mapDomainRingHom (R : Type u) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    {H : Type v} {K : Type w} [Group H] [Finite H] [Group K] [Finite K]
    (f : H →* K) :
    Continuous (MonoidAlgebra.mapDomainRingHom R f) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro k
  change Continuous fun x : MonoidAlgebra R H => (x.coeff.mapDomain f) k
  classical
  let _ := Fintype.ofFinite H
  by_cases hk : k ∈ Set.range f
  · obtain ⟨h, rfl⟩ := hk
    rw [show (fun x : MonoidAlgebra R H => (x.coeff.mapDomain f) (f h)) =
        (fun x => ∑ i : H with f i = f h, x.coeff i) by
      funext x
      rw [Finsupp.mapDomain_apply_eq_sum]
      apply Finset.sum_subset
      · intro i hi
        simp only [Finset.mem_filter] at hi ⊢
        exact ⟨Finset.mem_univ i, hi.2⟩
      · intro i hi hi'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp only [Finset.mem_filter] at hi'
        exact Finsupp.notMem_support_iff.mp fun hisupp => hi' ⟨hisupp, hi⟩]
    exact continuous_finsetSum _ fun i _ =>
      (continuous_apply i).comp continuous_induced_dom
  · rw [show (fun x : MonoidAlgebra R H => (x.coeff.mapDomain f) k) =
        (fun _ => 0) by
      funext x
      exact Finsupp.mapDomain_of_notMem_range x.coeff k hk]
    exact continuous_const

/-- A finite-index coefficient space is compact when
its coefficient ring is compact. -/
instance instCompactSpaceFiniteGroupAlgebra (R : Type u) [CommRing R]
    [TopologicalSpace R] [CompactSpace R]
    (H : Type v) [Finite H] : CompactSpace (MonoidAlgebra R H) :=
  (finiteGroupAlgebraHomeomorph R H).symm.compactSpace

private def toFiniteQuotients (R : Type u) [CommRing R]
    (G : ProfiniteGrp.{v}) :
    CompletedGroupAlgebra R G →
      ∀ U : OpenNormalSubgroup G, MonoidAlgebra R (G ⧸ U.toSubgroup) :=
  fun x U => proj R G U x

private def sectionsEquiv (R : Type u) [CommRing R]
    (G : ProfiniteGrp.{v}) :
    CompletedGroupAlgebra R G ≃
      (finiteQuotientSystem R G ⋙ forget RingCat).sections :=
  Types.isLimitEquivSections
    (isLimitOfPreserves (forget RingCat) (limit.isLimit (finiteQuotientSystem R G)))

@[simp]
private theorem sectionsEquiv_apply (R : Type u) [CommRing R]
    (G : ProfiniteGrp.{v}) (x : CompletedGroupAlgebra R G)
    (U : OpenNormalSubgroup G) :
    (sectionsEquiv R G x).1 U = proj R G U x :=
  rfl

private instance sectionsTopology (R : Type u) [CommRing R] [TopologicalSpace R]
    (G : ProfiniteGrp.{v}) :
    TopologicalSpace ((finiteQuotientSystem R G ⋙ forget RingCat).sections) :=
  .induced Subtype.val
    (@Pi.topologicalSpace (OpenNormalSubgroup G)
      (fun U => MonoidAlgebra R (G ⧸ U.toSubgroup))
      (fun U => finiteGroupAlgebraTopology R (G ⧸ U.toSubgroup)))

private def sectionsHomeomorph (R : Type u) [CommRing R] [TopologicalSpace R]
    (G : ProfiniteGrp.{v}) :
    CompletedGroupAlgebra R G ≃ₜ
      (finiteQuotientSystem R G ⋙ forget RingCat).sections := by
  exact
    { toEquiv := sectionsEquiv R G
      continuous_toFun := by
        apply continuous_induced_rng.mpr
        change Continuous (toFiniteQuotients R G)
        apply continuous_pi
        intro U
        exact continuous_proj R G U
      continuous_invFun := by
        rw [continuous_iff_proj]
        intro U
        change Continuous fun x :
          (finiteQuotientSystem R G ⋙ forget RingCat).sections =>
            proj R G U ((sectionsEquiv R G).symm x)
        convert
          ((@continuous_apply (OpenNormalSubgroup G)
          (fun U => MonoidAlgebra R (G ⧸ U.toSubgroup))
          (fun U => finiteGroupAlgebraTopology R (G ⧸ U.toSubgroup)) U).comp
            (@continuous_induced_dom
              ((finiteQuotientSystem R G ⋙ forget RingCat).sections)
              (∀ U : OpenNormalSubgroup G, MonoidAlgebra R (G ⧸ U.toSubgroup))
              Subtype.val
              (@Pi.topologicalSpace (OpenNormalSubgroup G)
                (fun U => MonoidAlgebra R (G ⧸ U.toSubgroup))
                (fun U => finiteGroupAlgebraTopology R (G ⧸ U.toSubgroup))))) using 1
        · rfl
        · rfl
        · funext x
          exact Types.isLimitEquivSections_symm_apply
            (isLimitOfPreserves (forget RingCat)
              (limit.isLimit (finiteQuotientSystem R G))) x U }

private instance compactSpaceSections (R : Type u) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]
    (G : ProfiniteGrp.{v}) :
    CompactSpace ((finiteQuotientSystem R G ⋙ forget RingCat).sections) := by
  change CompactSpace
    { x : ∀ U : OpenNormalSubgroup G, MonoidAlgebra R (G ⧸ U.toSubgroup) |
      ∀ {U V : OpenNormalSubgroup G} (f : U ⟶ V),
        (finiteQuotientSystem R G).map f (x U) = x V }
  rw [← isCompact_iff_compactSpace]
  apply IsClosed.isCompact
  have hset :
      { x : ∀ U : OpenNormalSubgroup G, MonoidAlgebra R (G ⧸ U.toSubgroup) |
        ∀ {U V : OpenNormalSubgroup G} (f : U ⟶ V),
          (finiteQuotientSystem R G).map f (x U) = x V } =
        ⋂ (U : OpenNormalSubgroup G) (V : OpenNormalSubgroup G) (f : U ⟶ V),
          { x | (finiteQuotientSystem R G).map f (x U) = x V } := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hset]
  apply isClosed_iInter
  intro U
  apply isClosed_iInter
  intro V
  apply isClosed_iInter
  intro f
  change IsClosed
    { x : ∀ U : OpenNormalSubgroup G, MonoidAlgebra R (G ⧸ U.toSubgroup) |
      MonoidAlgebra.mapDomainRingHom R
        (QuotientGroup.map U.toSubgroup V.toSubgroup (.id _) (leOfHom f)) (x U) = x V }
  apply isClosed_eq
  · exact (continuous_mapDomainRingHom R _).comp (continuous_apply U)
  · exact continuous_apply V

/-- A completed group algebra with its inverse-limit topology is compact when
its coefficient ring is compact and Hausdorff. -/
instance instCompactSpace (R : Type u) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [CompactSpace R] [T2Space R]
    (G : ProfiniteGrp.{v}) : CompactSpace (CompletedGroupAlgebra R G) :=
  (sectionsHomeomorph R G).symm.compactSpace

end CompletedGroupAlgebra
