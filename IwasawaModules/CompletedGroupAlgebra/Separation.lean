/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import IwasawaModules.CompletedGroupAlgebra.Topology

/-!
# Separation of completed group algebras

This file proves that the coefficientwise topology on a finite group algebra
and the inverse-limit topology on a completed group algebra are Hausdorff when
the coefficient ring is Hausdorff.

Compactness is supplied separately in
`IwasawaModules.CompletedGroupAlgebra.Compactness`. No completeness or density
assertion is made here.
-/

public section

set_option warningAsError true

noncomputable section

universe u v

namespace CompletedGroupAlgebra

/-- A finite-index coefficient space is Hausdorff when
its coefficient ring is Hausdorff. -/
instance instT2SpaceFiniteGroupAlgebra (R : Type u) [CommRing R]
    [TopologicalSpace R] [T2Space R]
    (H : Type v) [Finite H] : T2Space (MonoidAlgebra R H) :=
  (finiteGroupAlgebraHomeomorph R H).symm.t2Space

/-- A completed group algebra with its inverse-limit topology is Hausdorff
when its coefficient ring is Hausdorff. -/
instance instT2Space (R : Type u) [CommRing R] [TopologicalSpace R] [T2Space R]
    (G : ProfiniteGrp.{v}) : T2Space (CompletedGroupAlgebra R G) := by
  apply T2Space.of_injective_continuous
    (f := fun x U => proj R G U x)
  · intro x y h
    apply ext R G x y
    intro U
    exact congrArg (fun f => f U) h
  · exact continuous_pi fun U => continuous_proj R G U

end CompletedGroupAlgebra
