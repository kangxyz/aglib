/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalFormal
public import Aglib.RingTheory.AdicCompletion.DiscreteValuationRing
public import Aglib.RingTheory.MvPowerSeries.GenericDomainCharZero

/-!
# General separability of the actual DVR polynomial-to-formal generic map

The generic map lifts the original polynomial evaluation into series over the
actual maximal-ideal completion. Its equality with that original evaluation is
proved. Characteristic zero requires no geometric-reducedness premise.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace PolynomialLocalRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

lemma completionAlgebraMap_injective :
    Function.Injective (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  intro x y h
  apply AdicCompletion.of_injective (maximalIdeal R) R
  simpa only [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply] using h

lemma completionFaithfulSMul : FaithfulSMul R (AdicCompletion (maximalIdeal R) R) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (completionAlgebraMap_injective R)

/-- The existing polynomial evaluation is literally the coefficientwise map
followed by the native polynomial inclusion. -/
lemma polynomialToFormalSeries_eq_coefficientMap (n : ℕ) :
    (polynomialToFormalSeries R n).toRingHom =
      MvPowerSeries.polynomialCoefficientMap (σ := Fin n)
        (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    change polynomialToFormalSeries R n (MvPolynomial.C r) = _
    simp only [polynomialToFormalSeries, MvPolynomial.aeval_C,
      MvPowerSeries.algebraMap_apply, MvPowerSeries.polynomialCoefficientMap,
      RingHom.comp_apply, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
      MvPolynomial.coe_C, MvPowerSeries.map_C]
  · intro i
    change polynomialToFormalSeries R n (MvPolynomial.X i) = _
    simp only [polynomialToFormalSeries, MvPolynomial.aeval_X,
      MvPowerSeries.polynomialCoefficientMap, RingHom.comp_apply,
      MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_X,
      MvPowerSeries.map_X]

/-- The actual generic map lifting the original polynomial evaluation. -/
abbrev formalGenericFractionMap (n : ℕ) :
    FractionRing (MvPolynomial (Fin n) R) →+* FractionRing (FormalSeries R n) :=
  MvPowerSeries.polynomialSeriesFractionMap
    (algebraMap R (AdicCompletion (maximalIdeal R) R)) (completionAlgebraMap_injective R)

/-- This is the generator triangle for the original evaluation, not an arbitrary
embedding into a field of formal series. -/
lemma formalGenericFractionMap_algebraMap (n : ℕ) (q : MvPolynomial (Fin n) R) :
    formalGenericFractionMap R n (algebraMap _ (FractionRing (MvPolynomial (Fin n) R)) q) =
      algebraMap _ (FractionRing (FormalSeries R n)) (polynomialToFormalSeries R n q) := by
  rw [show polynomialToFormalSeries R n q =
      MvPowerSeries.polynomialCoefficientMap
        (algebraMap R (AdicCompletion (maximalIdeal R) R)) q from
    RingHom.congr_fun (polynomialToFormalSeries_eq_coefficientMap R n) q]
  exact MvPowerSeries.polynomialSeriesFractionMap_algebraMap _ _ q

/-- The intrinsic coefficient criterion supplies the actual completed generic map.
This theorem does not replace geometric reducedness by an unproved excellence bridge. -/
lemma isTranscendentalSeparable_formalGenericFractionMap (n : ℕ) :
    let := completionFaithfulSMul R
    let := FractionRing.liftAlgebra R (FractionRing (AdicCompletion (maximalIdeal R) R))
    let := (formalGenericFractionMap R n).toAlgebra
    Algebra.IsGeometricallyReduced (FractionRing R)
      (FractionRing (AdicCompletion (maximalIdeal R) R)) →
    Algebra.IsTranscendentalSeparable (FractionRing (MvPolynomial (Fin n) R))
      (FractionRing (FormalSeries R n)) := by
  let := completionFaithfulSMul R
  exact MvPowerSeries.isTranscendentalSeparable_domainFractionRing R
    (AdicCompletion (maximalIdeal R) R) (Fin n)

/-- In characteristic zero the actual completed generic map is generally
separable without a coefficient criterion or an excellence hypothesis. -/
lemma isTranscendentalSeparable_formalGenericFractionMap_of_charZero
    [CharZero R] (n : ℕ) :
    let := (formalGenericFractionMap R n).toAlgebra
    Algebra.IsTranscendentalSeparable (FractionRing (MvPolynomial (Fin n) R))
      (FractionRing (FormalSeries R n)) := by
  let := completionFaithfulSMul R
  exact MvPowerSeries.isTranscendentalSeparable_domainFractionRing_of_charZero R
    (AdicCompletion (maximalIdeal R) R) (Fin n)

end PolynomialLocalRing
