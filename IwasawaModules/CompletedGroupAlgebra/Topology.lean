/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import IwasawaModules.CompletedGroupAlgebra.Basic
public import Mathlib.Topology.Algebra.Monoid.FunOnFinite

/-!
# Topology on completed group algebras

This file gives each finite group algebra `R[H]` its coefficientwise product
topology when `R` is a topological commutative ring and `H` is finite. It then
equips `CompletedGroupAlgebra R G` with the inverse-limit topology induced by
its finite-quotient projections.

The resulting completed group algebra is a topological ring. A map into it is
continuous exactly when all of its finite-quotient coordinates are continuous.
Hausdorff separation and compactness are supplied separately in
`IwasawaModules.CompletedGroupAlgebra.Separation` and
`IwasawaModules.CompletedGroupAlgebra.Compactness`. No completeness or density
assertion is made here.
-/

public section

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Topology

universe u v

namespace CompletedGroupAlgebra

/-- For a finite index type `H`, the underlying coefficient space of its
monoid algebra is equivalent to `H → R`; no group structure on `H` is needed. -/
@[expose] def finiteGroupAlgebraCoefficients (R : Type u) [CommRing R]
    (H : Type v) [Finite H] : MonoidAlgebra R H ≃ (H → R) :=
  MonoidAlgebra.coeffEquiv.trans Finsupp.equivFunOnFinite

/-- The coefficientwise product topology for a finite index type. -/
@[expose, instance_reducible]
def finiteGroupAlgebraTopology (R : Type u) [CommRing R] [TopologicalSpace R]
    (H : Type v) [Finite H] : TopologicalSpace (MonoidAlgebra R H) :=
  .induced (finiteGroupAlgebraCoefficients R H) inferInstance

/-- The coefficientwise product topology on a finite-index coefficient space. -/
instance instTopologicalSpaceFiniteGroupAlgebra (R : Type u) [CommRing R]
    [TopologicalSpace R] (H : Type v) [Finite H] :
    TopologicalSpace (MonoidAlgebra R H) :=
  finiteGroupAlgebraTopology R H

/-- A finite-index coefficient space with its topology is homeomorphic
to the finite product of copies of its coefficient ring. -/
@[expose] def finiteGroupAlgebraHomeomorph (R : Type u) [CommRing R] [TopologicalSpace R]
    (H : Type v) [Finite H] : MonoidAlgebra R H ≃ₜ (H → R) where
  toEquiv := finiteGroupAlgebraCoefficients R H
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    convert (continuous_id : Continuous (id : (H → R) → (H → R))) using 1
    funext x
    exact (finiteGroupAlgebraCoefficients R H).apply_symm_apply x

/-- The coefficientwise product ring topology on the group algebra of a finite
group. -/
@[expose] def finiteGroupAlgebraRingTopology (R : Type u) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    (H : Type v) [Group H] [Finite H] : RingTopology (MonoidAlgebra R H) where
  toTopologicalSpace := finiteGroupAlgebraTopology R H
  continuous_add := by
    let _ : TopologicalSpace (MonoidAlgebra R H) :=
      finiteGroupAlgebraTopology R H
    apply continuous_induced_rng.mpr
    have hx : Continuous (fun z : MonoidAlgebra R H × MonoidAlgebra R H =>
        finiteGroupAlgebraCoefficients R H z.1) :=
      continuous_induced_dom.comp continuous_fst
    have hy : Continuous (fun z : MonoidAlgebra R H × MonoidAlgebra R H =>
        finiteGroupAlgebraCoefficients R H z.2) :=
      continuous_induced_dom.comp continuous_snd
    exact hx.add hy
  continuous_mul := by
    let _ : TopologicalSpace (MonoidAlgebra R H) :=
      finiteGroupAlgebraTopology R H
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro g
    classical
    let _ := Fintype.ofFinite H
    change Continuous fun z : MonoidAlgebra R H × MonoidAlgebra R H =>
      (z.1 * z.2).coeff g
    simp only [MonoidAlgebra.coeff_mul_apply_left]
    rw [show (fun z : MonoidAlgebra R H × MonoidAlgebra R H =>
        z.1.coeff.sum fun h r => r * z.2.coeff (h⁻¹ * g)) =
        (fun z => ∑ h, z.1.coeff h * z.2.coeff (h⁻¹ * g)) by
      funext z
      exact Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
    have hx : Continuous (fun z : MonoidAlgebra R H × MonoidAlgebra R H =>
        finiteGroupAlgebraCoefficients R H z.1) :=
      continuous_induced_dom.comp continuous_fst
    have hy : Continuous (fun z : MonoidAlgebra R H × MonoidAlgebra R H =>
        finiteGroupAlgebraCoefficients R H z.2) :=
      continuous_induced_dom.comp continuous_snd
    exact continuous_finsetSum _ fun h _ =>
      ((continuous_apply h).comp hx).mul ((continuous_apply (h⁻¹ * g)).comp hy)
  continuous_neg := by
    let _ : TopologicalSpace (MonoidAlgebra R H) :=
      finiteGroupAlgebraTopology R H
    apply continuous_induced_rng.mpr
    have h : Continuous (finiteGroupAlgebraCoefficients R H) :=
      continuous_induced_dom
    exact h.neg

/-- A finite group algebra is a topological ring for the coefficientwise
product topology. -/
instance instIsTopologicalRingFiniteGroupAlgebra (R : Type u) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    (H : Type v) [Group H] [Finite H] : IsTopologicalRing (MonoidAlgebra R H) :=
  (finiteGroupAlgebraRingTopology R H).toIsTopologicalRing

/-- The inverse-limit topology on a completed group algebra, induced by all
finite-quotient projections. -/
@[expose, instance_reducible]
def inverseLimitTopology (R : Type u) [CommRing R] [TopologicalSpace R]
    (G : ProfiniteGrp.{v}) : TopologicalSpace (CompletedGroupAlgebra R G) :=
  ⨅ U, .induced (proj R G U)
    (finiteGroupAlgebraTopology R (G ⧸ U.toSubgroup))

/-- The ring topology underlying the inverse-limit topology on a completed
group algebra. -/
@[expose] def ringTopology (R : Type u) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (G : ProfiniteGrp.{v}) :
    RingTopology (CompletedGroupAlgebra R G) where
  toTopologicalSpace := inverseLimitTopology R G
  continuous_add := by
    let _ : TopologicalSpace (CompletedGroupAlgebra R G) := inverseLimitTopology R G
    apply continuous_iInf_rng.mpr
    intro U
    apply continuous_induced_rng.mpr
    let _ : TopologicalSpace (MonoidAlgebra R (G ⧸ U.toSubgroup)) :=
      (finiteGroupAlgebraRingTopology R (G ⧸ U.toSubgroup)).toTopologicalSpace
    let _ : IsTopologicalRing (MonoidAlgebra R (G ⧸ U.toSubgroup)) :=
      (finiteGroupAlgebraRingTopology R (G ⧸ U.toSubgroup)).toIsTopologicalRing
    have hp : Continuous[inverseLimitTopology R G,
        (finiteGroupAlgebraRingTopology R
          (G ⧸ U.toSubgroup)).toTopologicalSpace] (proj R G U) :=
      continuous_iInf_dom continuous_induced_dom
    change Continuous fun z : CompletedGroupAlgebra R G × CompletedGroupAlgebra R G =>
      proj R G U (z.1 + z.2)
    rw [show (fun z : CompletedGroupAlgebra R G × CompletedGroupAlgebra R G =>
        proj R G U (z.1 + z.2)) =
        (fun z => proj R G U z.1 + proj R G U z.2) by
      funext z
      exact map_add (proj R G U) z.1 z.2]
    exact (hp.comp continuous_fst).add (hp.comp continuous_snd)
  continuous_mul := by
    let _ : TopologicalSpace (CompletedGroupAlgebra R G) := inverseLimitTopology R G
    apply continuous_iInf_rng.mpr
    intro U
    apply continuous_induced_rng.mpr
    let _ : TopologicalSpace (MonoidAlgebra R (G ⧸ U.toSubgroup)) :=
      (finiteGroupAlgebraRingTopology R (G ⧸ U.toSubgroup)).toTopologicalSpace
    let _ : IsTopologicalRing (MonoidAlgebra R (G ⧸ U.toSubgroup)) :=
      (finiteGroupAlgebraRingTopology R (G ⧸ U.toSubgroup)).toIsTopologicalRing
    have hp : Continuous[inverseLimitTopology R G,
        (finiteGroupAlgebraRingTopology R
          (G ⧸ U.toSubgroup)).toTopologicalSpace] (proj R G U) :=
      continuous_iInf_dom continuous_induced_dom
    change Continuous fun z : CompletedGroupAlgebra R G × CompletedGroupAlgebra R G =>
      proj R G U (z.1 * z.2)
    rw [show (fun z : CompletedGroupAlgebra R G × CompletedGroupAlgebra R G =>
        proj R G U (z.1 * z.2)) =
        (fun z => proj R G U z.1 * proj R G U z.2) by
      funext z
      exact map_mul (proj R G U) z.1 z.2]
    exact (hp.comp continuous_fst).mul (hp.comp continuous_snd)
  continuous_neg := by
    let _ : TopologicalSpace (CompletedGroupAlgebra R G) := inverseLimitTopology R G
    apply continuous_iInf_rng.mpr
    intro U
    apply continuous_induced_rng.mpr
    let _ : TopologicalSpace (MonoidAlgebra R (G ⧸ U.toSubgroup)) :=
      (finiteGroupAlgebraRingTopology R (G ⧸ U.toSubgroup)).toTopologicalSpace
    let _ : IsTopologicalRing (MonoidAlgebra R (G ⧸ U.toSubgroup)) :=
      (finiteGroupAlgebraRingTopology R (G ⧸ U.toSubgroup)).toIsTopologicalRing
    have hp : Continuous[inverseLimitTopology R G,
        (finiteGroupAlgebraRingTopology R
          (G ⧸ U.toSubgroup)).toTopologicalSpace] (proj R G U) :=
      continuous_iInf_dom continuous_induced_dom
    change Continuous fun z : CompletedGroupAlgebra R G => proj R G U (-z)
    rw [show (fun z : CompletedGroupAlgebra R G => proj R G U (-z)) =
        (fun z => -(proj R G U z)) by
      funext z
      exact map_neg (proj R G U) z]
    exact hp.neg

/-- The inverse-limit topology on a completed group algebra. -/
instance instTopologicalSpace (R : Type u) [CommRing R] [TopologicalSpace R]
    (G : ProfiniteGrp.{v}) : TopologicalSpace (CompletedGroupAlgebra R G) :=
  inverseLimitTopology R G

/-- A completed group algebra is a topological ring for its inverse-limit
topology. -/
instance instIsTopologicalRing (R : Type u) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (G : ProfiniteGrp.{v}) :
    IsTopologicalRing (CompletedGroupAlgebra R G) :=
  (ringTopology R G).toIsTopologicalRing

/-- Every finite-quotient projection from a completed group algebra is
continuous. -/
theorem continuous_proj (R : Type u) [CommRing R] [TopologicalSpace R]
    (G : ProfiniteGrp.{v}) (U : OpenNormalSubgroup G) :
    Continuous (proj R G U) := by
  change Continuous[inverseLimitTopology R G,
    finiteGroupAlgebraTopology R (G ⧸ U.toSubgroup)] (proj R G U)
  exact continuous_iInf_dom continuous_induced_dom

/-- A map to a completed group algebra is continuous if and only if all of its
finite-quotient coordinates are continuous. -/
theorem continuous_iff_proj {X : Type*} [TopologicalSpace X]
    (R : Type u) [CommRing R] [TopologicalSpace R]
    (G : ProfiniteGrp.{v}) (f : X → CompletedGroupAlgebra R G) :
    Continuous f ↔ ∀ U, Continuous (proj R G U ∘ f) := by
  change Continuous[_, inverseLimitTopology R G] f ↔ _
  rw [continuous_iInf_rng]
  apply forall_congr'
  intro U
  exact continuous_induced_rng

end CompletedGroupAlgebra
