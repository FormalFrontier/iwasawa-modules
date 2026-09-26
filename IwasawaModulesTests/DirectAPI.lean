/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import IwasawaModules.PseudoIsomorphism.LinearMap
import IwasawaModules.CompletedGroupAlgebra.Completeness
import Mathlib.Topology.Instances.ZMod

/-!
# Direct-leaf clients

These examples avoid the production aggregate root and the other test leaf.
The extra mathlib import supplies concrete `ZMod` coefficient fixtures.
-/

set_option warningAsError true

noncomputable section

namespace IwasawaModulesTests.DirectAPI

/-- The finite coefficient ring below is nonzero. -/
theorem binary_coefficients_nonzero : (1 : ZMod 2) ≠ 0 := by decide

/-- The two transpositions in the group used below do not commute. -/
theorem transpositions_noncommute :
    (Equiv.swap (0 : Fin 3) 1) * (Equiv.swap 1 2) ≠
      (Equiv.swap 1 2) * (Equiv.swap 0 1) := by decide

/-- The zero coefficient ring and degenerate module are accepted. -/
theorem zero_ring_identity :
    (LinearMap.id : ZMod 1 →ₗ[ZMod 1] ZMod 1).IsPseudoIsomorphism (ZMod 1) :=
  LinearMap.isPseudoIsomorphism_id (ZMod 1)

/-- Composition over the zero ring remains directional. -/
theorem zero_ring_composition :
    ((LinearMap.id : ZMod 1 →ₗ[ZMod 1] ZMod 1).comp
      (LinearMap.id : ZMod 1 →ₗ[ZMod 1] ZMod 1)).IsPseudoIsomorphism (ZMod 1) :=
  (LinearMap.isPseudoIsomorphism_id (ZMod 1)).comp (ZMod 1)
    (LinearMap.isPseudoIsomorphism_id (ZMod 1))

variable (G : ProfiniteGrp)

/-- Zero coefficients still admit the ordinary-to-completed projection. -/
theorem zero_coefficients (U : OpenNormalSubgroup G) (a : MonoidAlgebra (ZMod 1) G) :
    CompletedGroupAlgebra.proj (ZMod 1) G U
        (CompletedGroupAlgebra.ofMonoidAlgebra (ZMod 1) G a) =
      MonoidAlgebra.mapDomainRingHom (ZMod 1) (QuotientGroup.mk' U.toSubgroup) a :=
  CompletedGroupAlgebra.proj_ofMonoidAlgebra (ZMod 1) G U a

/-- An ordinary group algebra of a noncommutative group is still a ring. -/
theorem finite_permutation_ring_assoc
    (a b c : MonoidAlgebra (ZMod 2) (Equiv.Perm (Fin 3))) :
    (a * b) * c = a * (b * c) := mul_assoc a b c

/-- The completed ring likewise supports this finite nonabelian group. -/
theorem finite_permutation_completion_assoc
    (a b c : CompletedGroupAlgebra (ZMod 2)
      (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Equiv.Perm (Fin 3))))) :
    (a * b) * c = a * (b * c) := mul_assoc a b c

/-- The finite noncommutative algebra is compact over binary coefficients. -/
theorem finite_permutation_compact :
    CompactSpace (MonoidAlgebra (ZMod 2) (Equiv.Perm (Fin 3))) := inferInstance

/-- The same finite profinite group has a Hausdorff compact completion. -/
theorem finite_permutation_complete :
    CompleteSpace (CompletedGroupAlgebra (ZMod 2)
      (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Equiv.Perm (Fin 3))))) := inferInstance

/-- The nonzero finite-coefficient projection is computable at the ring API. -/
theorem finite_permutation_projection
    (U : OpenNormalSubgroup
      (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Equiv.Perm (Fin 3)))))
    (a : MonoidAlgebra (ZMod 2)
      (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Equiv.Perm (Fin 3))))) :
    CompletedGroupAlgebra.proj (ZMod 2) _ U
        (CompletedGroupAlgebra.ofMonoidAlgebra (ZMod 2) _ a) =
      MonoidAlgebra.mapDomainRingHom (ZMod 2) (QuotientGroup.mk' U.toSubgroup) a :=
  CompletedGroupAlgebra.proj_ofMonoidAlgebra (ZMod 2) _ U a

end IwasawaModulesTests.DirectAPI
