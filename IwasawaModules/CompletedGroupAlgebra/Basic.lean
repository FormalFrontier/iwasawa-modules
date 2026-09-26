/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

/-!
# Finite-quotient group-algebra limits

This file defines the underlying ring of the inverse limit of the ordinary
group algebras `R[G/U]` as `U` ranges over the open normal subgroups of a
profinite group `G`. The construction uses `RingCat`, so `G` need not be
commutative.

The inverse-limit topology and its universal property are supplied separately
in `IwasawaModules.CompletedGroupAlgebra.Topology`. Compact modules over the
resulting topological ring remain deferred.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CompletedGroupAlgebra

/-- Ordinary monoid algebras over `R`, functorial in arbitrary monoids.

The codomain is `RingCat`, rather than `CommRingCat`, because the monoids and
their monoid algebras need not be commutative. -/
@[expose] def monoidAlgebraFunctor (R : Type u) [CommRing R] : MonCat.{v} ⥤ RingCat.{max u v} where
  obj M := RingCat.of (MonoidAlgebra R M)
  map f := RingCat.ofHom (MonoidAlgebra.mapDomainRingHom R f.hom)
  map_id M := by
    ext <;> simp
  map_comp f g := by
    ext <;> simp

/-- The inverse system `U ↦ R[G/U]` over the open normal subgroups of a
profinite group `G`. -/
@[expose] def finiteQuotientSystem (R : Type u) [CommRing R] (G : ProfiniteGrp.{v}) :
    OpenNormalSubgroup G ⥤ RingCat.{max u v} :=
  ProfiniteGrp.diagram G ⋙
    forget₂ ProfiniteGrp GrpCat.{v} ⋙
    forget₂ GrpCat MonCat.{v} ⋙
    monoidAlgebraFunctor R

/-- The underlying ring of the inverse limit of `R[G/U]` over all open normal
subgroups `U` of `G`.

The topology is asserted separately in
`IwasawaModules.CompletedGroupAlgebra.Topology`. -/
abbrev _root_.CompletedGroupAlgebra (R : Type u) [CommRing R] (G : ProfiniteGrp.{v}) :=
  limit (finiteQuotientSystem R G)

/-- Projection from the finite-quotient group-algebra limit to one coordinate
`R[G/U]`. -/
@[expose] def proj (R : Type u) [CommRing R] (G : ProfiniteGrp.{v}) (U : OpenNormalSubgroup G) :
    CompletedGroupAlgebra R G →+* MonoidAlgebra R (G ⧸ U.toSubgroup) :=
  (limit.π (finiteQuotientSystem R G) U).hom

/-- Two elements of a finite-quotient group-algebra limit are equal when all
their finite-quotient coordinates are equal. -/
@[ext]
theorem ext (R : Type u) [CommRing R] (G : ProfiniteGrp.{v})
    (x y : CompletedGroupAlgebra R G)
    (h : ∀ U, proj R G U x = proj R G U y) : x = y :=
  Concrete.limit_ext (finiteQuotientSystem R G) x y h

/-- The ordinary group algebra `R[G]` maps compatibly to all finite-quotient
group algebras. -/
@[expose] def ordinaryCone (R : Type u) [CommRing R] (G : ProfiniteGrp.{v}) :
    Cone (finiteQuotientSystem R G) where
  pt := RingCat.of (MonoidAlgebra R G)
  π :=
    { app := fun U => RingCat.ofHom
        (MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' U.toSubgroup))
      naturality := by
        intro U V f
        change RingCat.ofHom (MonoidAlgebra.mapDomainRingHom R
            (QuotientGroup.mk' V.toSubgroup)) =
          RingCat.ofHom ((MonoidAlgebra.mapDomainRingHom R
            (QuotientGroup.map U.toSubgroup V.toSubgroup (.id _) (leOfHom f))).comp
              (MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' U.toSubgroup)))
        apply RingCat.hom_ext
        rw [← MonoidAlgebra.mapDomainRingHom_comp]
        congr 1 }

/-- The canonical ring homomorphism from the ordinary group algebra to its
finite-quotient inverse limit. -/
@[expose] def ofMonoidAlgebra (R : Type u) [CommRing R] (G : ProfiniteGrp.{v}) :
    MonoidAlgebra R G →+* CompletedGroupAlgebra R G :=
  ((limit.isLimit (finiteQuotientSystem R G)).lift (ordinaryCone R G)).hom

@[simp]
theorem proj_ofMonoidAlgebra (R : Type u) [CommRing R] (G : ProfiniteGrp.{v})
    (U : OpenNormalSubgroup G) (x : MonoidAlgebra R G) :
    proj R G U (ofMonoidAlgebra R G x) =
      MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' U.toSubgroup) x := by
  exact DFunLike.congr_fun (congrArg RingCat.Hom.hom
    ((limit.isLimit (finiteQuotientSystem R G)).fac (ordinaryCone R G) U)) x

/-- The coordinate projections satisfy the expected quotient compatibility. -/
theorem proj_compatibility (R : Type u) [CommRing R] (G : ProfiniteGrp.{v})
    {U V : OpenNormalSubgroup G} (h : U ≤ V) (x : CompletedGroupAlgebra R G) :
    MonoidAlgebra.mapDomainRingHom R
        (QuotientGroup.map U.toSubgroup V.toSubgroup (.id _) h) (proj R G U x) =
      proj R G V x := by
  exact DFunLike.congr_fun (congrArg RingCat.Hom.hom
    (limit.w (finiteQuotientSystem R G) (homOfLE h))) x

end CompletedGroupAlgebra
