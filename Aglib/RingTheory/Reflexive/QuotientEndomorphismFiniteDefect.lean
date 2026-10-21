/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Reflexive.QuotientEndomorphismLocalization
public import Aglib.RingTheory.Support.FiniteDefect

/-! Finite-length cokernel of the actual quotient-endomorphism map under punctured projectivity. -/

@[expose] public section

noncomputable section

open scoped Pointwise

namespace QuotSMulTop

variable {R : Type*} [CommRing R] (a : R) (M : Type*) [AddCommGroup M] [Module R M]

/-- The quotient of the original endomorphism module maps surjectively after localization
where the original localized module is projective. -/
theorem localized_quotientEndomorphism_surjective
    (S : Submonoid R) [Module.FinitePresentation R M]
    [Module.FinitePresentation R (QuotSMulTop a M)]
    [Module.Projective (Localization S) (LocalizedModule S M)] :
    Function.Surjective (LocalizedModule.map S ((quotientEndomorphism a M).restrictScalars R)) := by
  let U := QuotSMulTop a M
  let E := Module.End R M
  let F := Module.End (R ⧸ Ideal.span {a}) U
  let q : E →ₗ[R] QuotSMulTop a E := (a • (⊤ : Submodule R E)).mkQ
  let e : Module.End R U ≃ₗ[R] F :=
    LinearMap.extendScalarsOfSurjectiveEquiv Ideal.Quotient.mk_surjective
  have hm := localized_map_surjective_of_projective (Rₛ := Localization S) S
    (LocalizedModule.mkLinearMap S M) a
  have he := LocalizedModule.map_surjective S e.toLinearMap e.surjective
  have hcomp : (LocalizedModule.map S ((quotientEndomorphism a M).restrictScalars R)).comp
      (LocalizedModule.map S q) =
    (LocalizedModule.map S e.toLinearMap).comp (LocalizedModule.map S (QuotSMulTop.map a)) := by
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.linearMap_ext S (LocalizedModule.mkLinearMap S E)
      (LocalizedModule.mkLinearMap S F)
    apply LinearMap.ext
    intro f
    simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply,
      LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk]
    rfl
  have hs : Function.Surjective ((LocalizedModule.map S e.toLinearMap).comp
      (LocalizedModule.map S (QuotSMulTop.map a))) := he.comp hm
  rw [← hcomp] at hs
  exact Function.Surjective.of_comp hs

/-- Punctured projectivity makes the cokernel of the actual quotient-endomorphism map
finite length over the quotient ring. -/
theorem isFiniteLength_coker_quotientEndomorphism
    [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M]
    (hfree : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Module.Projective (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M)) :
    IsFiniteLength (R ⧸ Ideal.span {a})
      (Module.End (R ⧸ Ideal.span {a}) (QuotSMulTop a M) ⧸ (quotientEndomorphism a M).range) := by
  let Q := R ⧸ Ideal.span {a}
  let U := QuotSMulTop a M
  let e : Module.End R U ≃ₗ[R] Module.End Q U :=
    LinearMap.extendScalarsOfSurjectiveEquiv Ideal.Quotient.mk_surjective
  let := Module.Finite.equiv e
  let := Module.finitePresentation_of_finite R M
  let := Module.finitePresentation_of_finite R U
  have hR := LinearMap.isFiniteLength_coker_of_surjective_punctured
    ((quotientEndomorphism a M).restrictScalars R) (fun p hp ↦ by
      let := hfree p hp
      exact localized_quotientEndomorphism_surjective a M p.asIdeal.primeCompl)
  rw [LinearMap.range_restrictScalars] at hR
  have hQ := LinearEquiv.isFiniteLength
    (Submodule.Quotient.restrictScalarsEquiv R (quotientEndomorphism a M).range) hR
  obtain ⟨hN, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hQ
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_of_tower R hN, isArtinian_of_tower R hA⟩

end QuotSMulTop
