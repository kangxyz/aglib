/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Reflexive.AuslanderDimensionThree
public import Aglib.RingTheory.Reflexive.QuotientBidualFree
public import Aglib.RingTheory.Reflexive.QuotientEndomorphismPi
public import Aglib.RingTheory.RegularLocalRing.Parameters

/-!
# The punctured-free local Auslander criterion

Induction on the dimension uses the actual regular-parameter quotient and its
bidual. Dimensions at most two follow from the reflexive projective-dimension
bound; dimension three uses the finite-length Euler obstruction. Above dimension
three, finite-defect Ext comparisons and dual freeness lifting finish the step.

Punctured freeness remains an explicit hypothesis. This does not assert that
arbitrary localizations of a regular local ring are regular; the separate ambient
regular-ring criterion supplies punctured freeness by its own induction.
-/

@[expose] public section

noncomputable section

universe u

namespace ModuleCat

/-- The punctured-free criterion, with dimension exposed for its actual induction. -/
theorem free_of_endomorphism_equiv_of_free_punctured_of_dimension (d : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
      ringKrullDim R = (d : ℕ) →
      ∀ (M : ModuleCat.{u} R) [Module.Finite R M] [Module.IsReflexive R M]
        (r : ℕ), (Module.End R M ≃ₗ[R] (Fin r → M)) →
        (∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
          Module.Free (Localization.AtPrime p.asIdeal)
            (LocalizedModule p.asIdeal.primeCompl M)) → Module.Free R M := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro R instR instRegular hd M instFinite instReflexive r eEnd hfree
    by_cases h2 : d ≤ 2
    · exact Module.free_of_isReflexive_of_dimension_le_two R
        (by rw [hd]; exact_mod_cast h2) M
    by_cases h3 : d = 3
    · exact free_of_endomorphism_equiv_of_free_punctured_of_dimension_three R
        (by simpa [h3] using hd) M r eEnd hfree
    have h4 : 4 ≤ d := by omega
    have hdstep : ringKrullDim R = ((d - 1) + 1 : ℕ) := by
      rw [hd, Nat.sub_add_cancel (by omega : 1 ≤ d)]
    obtain ⟨a, ham, ha, hQ, hdimQ⟩ :=
      IsRegularLocalRing.exists_regular_parameter R (d - 1) hdstep
    let Q := R ⧸ Ideal.span {a}
    let U := QuotSMulTop a M
    let N := Module.Dual Q (Module.Dual Q U)
    have : IsRegularLocalRing Q := hQ
    have : IsDomain Q := IsRegularLocalRing.isDomain_of_regularLocal Q
    have : Module.Finite Q U := Module.Finite.of_restrictScalars_finite R Q U
    have : Module.IsReflexive Q N :=
      Module.IsReflexive.dual_of_finite (R := Q) (M := Module.Dual Q U)
    have hareg : IsRegular a :=
      (Commute.isRegular_iff (fun b ↦ mul_comm a b)).mpr ha
    have haM : IsSMulRegular M a := hareg.isSMulRegular
    have hU := QuotSMulTop.free_punctured_of_free_punctured a M hfree
    have hN := Module.free_punctured_doubleDual_of_free_punctured hU
    let eN := QuotSMulTop.quotientBidualEndomorphismPiEquiv a M haM hfree eEnd
      (d - 1) hdimQ (by omega)
    have : Module.Free Q N :=
      ih (d - 1) (by omega) Q hdimQ (ModuleCat.of Q N) r eN hN
    exact Module.free_of_free_quotient_doubleDual M a ha haM ham
      (d - 1) hdimQ (by omega) hU

/-- A finite reflexive module over a regular local ring is free when its actual
endomorphism module is a finite power of itself and it is punctured-free. -/
theorem free_of_endomorphism_equiv_of_free_punctured
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Module.IsReflexive R M]
    (r : ℕ) (eEnd : Module.End R M ≃ₗ[R] (Fin r → M))
    (hfree : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Module.Free (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M)) : Module.Free R M :=
  free_of_endomorphism_equiv_of_free_punctured_of_dimension
    (IsLocalRing.maximalIdeal R).spanFinrank R
    IsRegularLocalRing.spanFinrank_maximalIdeal.symm M r eEnd hfree

end ModuleCat
