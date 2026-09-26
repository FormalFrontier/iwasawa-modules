/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import IwasawaModules.CompletedGroupAlgebra.Compactness
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Completeness of compact completed group algebras

This file equips finite and completed group algebras with the canonical right
uniformity of their additive topological groups. Since their additive groups
are commutative, this is an additive-group uniformity. Compact completed group
algebras, and their finite levels, are complete for this uniformity.

This is the compact-Hausdorff completeness route. Completeness of completed
group algebras over merely complete Hausdorff coefficient rings requires a
separate inverse-limit argument and is not asserted here.
-/

public section

set_option warningAsError true

noncomputable section

universe u v

namespace CompletedGroupAlgebra

/-- The canonical additive-group uniformity on a finite group algebra with its
coefficientwise topology. -/
@[expose, instance_reducible]
def finiteGroupAlgebraUniformSpace (R : Type u) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    (H : Type v) [Group H] [Finite H] : UniformSpace (MonoidAlgebra R H) :=
  IsTopologicalAddGroup.rightUniformSpace (MonoidAlgebra R H)

/-- The canonical uniformity induces the existing coefficientwise topology. -/
theorem finiteGroupAlgebraUniformSpace_toTopologicalSpace (R : Type u)
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (H : Type v) [Group H] [Finite H] :
    (finiteGroupAlgebraUniformSpace R H).toTopologicalSpace =
      finiteGroupAlgebraTopology R H :=
  rfl

/-- The canonical additive-group uniformity on a finite group algebra. -/
instance instUniformSpaceFiniteGroupAlgebra (R : Type u) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    (H : Type v) [Group H] [Finite H] : UniformSpace (MonoidAlgebra R H) :=
  finiteGroupAlgebraUniformSpace R H

/-- A finite group algebra is a uniform additive group for its canonical
additive-group uniformity. -/
instance instIsUniformAddGroupFiniteGroupAlgebra (R : Type u) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    (H : Type v) [Group H] [Finite H] : IsUniformAddGroup (MonoidAlgebra R H) :=
  isUniformAddGroup_of_addCommGroup

/-- A compact finite group algebra is complete for its canonical
additive-group uniformity. -/
instance instCompleteSpaceFiniteGroupAlgebra (R : Type u) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
    (H : Type v) [Group H] [Finite H] : CompleteSpace (MonoidAlgebra R H) :=
  IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace

/-- The canonical additive-group uniformity on a completed group algebra with
its inverse-limit topology. -/
@[expose, instance_reducible]
def completedGroupAlgebraUniformSpace (R : Type u) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (G : ProfiniteGrp.{v}) :
    UniformSpace (CompletedGroupAlgebra R G) :=
  IsTopologicalAddGroup.rightUniformSpace (CompletedGroupAlgebra R G)

/-- The canonical uniformity induces the existing inverse-limit topology. -/
theorem completedGroupAlgebraUniformSpace_toTopologicalSpace (R : Type u)
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (G : ProfiniteGrp.{v}) :
    (completedGroupAlgebraUniformSpace R G).toTopologicalSpace =
      inverseLimitTopology R G :=
  rfl

/-- The canonical additive-group uniformity on a completed group algebra. -/
instance instUniformSpace (R : Type u) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (G : ProfiniteGrp.{v}) :
    UniformSpace (CompletedGroupAlgebra R G) :=
  completedGroupAlgebraUniformSpace R G

/-- A completed group algebra is a uniform additive group for its canonical
additive-group uniformity. -/
instance instIsUniformAddGroup (R : Type u) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (G : ProfiniteGrp.{v}) :
    IsUniformAddGroup (CompletedGroupAlgebra R G) :=
  isUniformAddGroup_of_addCommGroup

/-- A completed group algebra over a compact Hausdorff coefficient ring is
complete for its canonical additive-group uniformity. -/
instance instCompleteSpace (R : Type u) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [CompactSpace R] [T2Space R]
    (G : ProfiniteGrp.{v}) : CompleteSpace (CompletedGroupAlgebra R G) :=
  IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace

end CompletedGroupAlgebra
