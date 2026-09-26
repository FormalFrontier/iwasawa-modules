/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import IwasawaModules.PseudoIsomorphism.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-!
# Directional pseudo-isomorphisms

A linear map is a pseudo-isomorphism when its kernel and cokernel are
pseudo-null. Equivalently its localization is bijective at every prime of
height at most one. The API proves composition, not symmetry or a reversal
criterion. Ring and module universes are independent.
-/

public section

set_option warningAsError true

namespace LinearMap

universe u v w

variable (R : Type u) [CommRing R]
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A linear map is a pseudo-isomorphism when its kernel and cokernel are
pseudo-null. This is directional data, not an equivalence between modules. -/
@[expose] def IsPseudoIsomorphism (f : M →ₗ[R] N) : Prop :=
  Module.IsPseudoNull R f.ker ∧ Module.IsPseudoNull R (N ⧸ f.range)

/-- Localization of a linear map is injective exactly when the localization of
its kernel is trivial. -/
theorem localizedMap_injective_iff_subsingleton_localized_ker
    (S : Submonoid R) (f : M →ₗ[R] N) :
    Function.Injective (LocalizedModule.map S f) ↔
      Subsingleton (LocalizedModule S f.ker) := by
  let fM := LocalizedModule.mkLinearMap S M
  let fN := LocalizedModule.mkLinearMap S N
  let lf := IsLocalizedModule.map S fM fN f
  let kf := LinearMap.toKerIsLocalized S fM fN f
  let _ : IsLocalizedModule S kf :=
    LinearMap.toKerLocalized_isLocalizedModule (Localization S) S fM fN f
  let e : LocalizedModule S f.ker ≃ₗ[R] lf.ker :=
    IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S f.ker) kf
  have hmap : (LocalizedModule.map S f).restrictScalars R = lf := rfl
  change Function.Injective ((LocalizedModule.map S f).restrictScalars R) ↔ _
  rw [hmap, ← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
  exact e.toEquiv.subsingleton_congr.symm

/-- The definition restated pointwise using localized kernels and cokernels. -/
theorem isPseudoIsomorphism_iff_localizedModule_subsingleton (f : M →ₗ[R] N) :
    f.IsPseudoIsomorphism R ↔
      (∀ p : PrimeSpectrum R, p.asIdeal.height ≤ 1 →
        Subsingleton (LocalizedModule p.asIdeal.primeCompl f.ker)) ∧
      (∀ p : PrimeSpectrum R, p.asIdeal.height ≤ 1 →
        Subsingleton (LocalizedModule p.asIdeal.primeCompl (N ⧸ f.range))) := by
  rw [IsPseudoIsomorphism, Module.isPseudoNull_iff_localizedModule_subsingleton,
    Module.isPseudoNull_iff_localizedModule_subsingleton]

/-- A linear map is a pseudo-isomorphism exactly when it becomes bijective at
every prime of height at most one. -/
theorem isPseudoIsomorphism_iff_localizedModule_map_bijective (f : M →ₗ[R] N) :
    f.IsPseudoIsomorphism R ↔
      ∀ p : PrimeSpectrum R, p.asIdeal.height ≤ 1 →
        Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl f) := by
  rw [IsPseudoIsomorphism]
  constructor
  · rintro ⟨hker, hcoker⟩ p hp
    constructor
    · rw [localizedMap_injective_iff_subsingleton_localized_ker]
      exact (Module.isPseudoNull_iff_localizedModule_subsingleton R f.ker).mp hker p hp
    · rw [LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker]
      exact (Module.isPseudoNull_iff_localizedModule_subsingleton R (N ⧸ f.range)).mp
        hcoker p hp
  · intro h
    constructor
    · rw [Module.isPseudoNull_iff_localizedModule_subsingleton]
      intro p hp
      rw [← localizedMap_injective_iff_subsingleton_localized_ker]
      exact (h p hp).injective
    · rw [Module.isPseudoNull_iff_localizedModule_subsingleton]
      intro p hp
      rw [← LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker]
      exact (h p hp).surjective

/-- Every bijective linear map is a pseudo-isomorphism. -/
theorem IsPseudoIsomorphism.of_bijective {f : M →ₗ[R] N}
    (hf : Function.Bijective f) : f.IsPseudoIsomorphism R := by
  constructor
  · rw [LinearMap.ker_eq_bot.mpr hf.1]
    exact Module.IsPseudoNull.of_subsingleton R (⊥ : Submodule R M)
  · rw [LinearMap.range_eq_top.mpr hf.2]
    exact Module.IsPseudoNull.of_subsingleton R (N ⧸ (⊤ : Submodule R N))

/-- The identity linear map is a pseudo-isomorphism. -/
theorem isPseudoIsomorphism_id :
    (LinearMap.id : M →ₗ[R] M).IsPseudoIsomorphism R :=
  IsPseudoIsomorphism.of_bijective R Function.bijective_id

/-- The composite of two pseudo-isomorphisms is a pseudo-isomorphism. -/
theorem IsPseudoIsomorphism.comp
    {P : Type*} [AddCommGroup P] [Module R P]
    {g : N →ₗ[R] P} {f : M →ₗ[R] N}
    (hg : g.IsPseudoIsomorphism R) (hf : f.IsPseudoIsomorphism R) :
    (g.comp f).IsPseudoIsomorphism R := by
  rw [isPseudoIsomorphism_iff_localizedModule_map_bijective] at hg hf ⊢
  intro p hp
  have hmap : LocalizedModule.map p.asIdeal.primeCompl (g.comp f) =
      (LocalizedModule.map p.asIdeal.primeCompl g).comp
        (LocalizedModule.map p.asIdeal.primeCompl f) := by
    apply LinearMap.restrictScalars_injective R
    exact IsLocalizedModule.map_comp' p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P) f g
  rw [hmap]
  exact (hg p hp).comp (hf p hp)

end LinearMap

namespace LinearEquiv

universe u v w

variable (R : Type u) [CommRing R]
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The linear map underlying a linear equivalence is a pseudo-isomorphism. -/
theorem isPseudoIsomorphism (e : M ≃ₗ[R] N) :
    e.toLinearMap.IsPseudoIsomorphism R :=
  LinearMap.IsPseudoIsomorphism.of_bijective R e.bijective

end LinearEquiv
