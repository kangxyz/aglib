/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPowerSeries.GenericDomainSeparable

/-!
# The characteristic-zero canonical generic extension

Perfectness of the actual source fraction field proves general separability
without any geometric-reducedness or excellence premise on the coefficient map.
-/

@[expose] public noncomputable section

namespace Algebra

/-- Every field extension of a perfect field is generally separable. This does
not claim that an arbitrary such extension is itself separably generated. -/
theorem isTranscendentalSeparable_of_perfectField
    (k L : Type*) [Field k] [Field L] [Algebra k L] [PerfectField k] :
    IsTranscendentalSeparable k L := by
  refine ⟨fun E hE => ?_⟩
  let := hE
  infer_instance

end Algebra

namespace MvPowerSeries

/-- The actual canonical generic polynomial-to-series map in characteristic zero
is generally separable. No coefficient geometric-reducedness premise is needed. -/
theorem isTranscendentalSeparable_domainFractionRing_of_charZero
    (R S σ : Type*) [CommRing R] [IsDomain R] [CharZero R]
    [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S] :
    let := (polynomialSeriesFractionMap (σ := σ) (algebraMap R S)
      (FaithfulSMul.algebraMap_injective R S)).toAlgebra
    Algebra.IsTranscendentalSeparable (FractionRing (MvPolynomial σ R))
      (FractionRing (MvPowerSeries σ S)) := by
  let := (polynomialSeriesFractionMap (σ := σ) (algebraMap R S)
    (FaithfulSMul.algebraMap_injective R S)).toAlgebra
  let : CharZero (FractionRing (MvPolynomial σ R)) := charZero_of_injective_ringHom
    (f := (algebraMap (MvPolynomial σ R) (FractionRing (MvPolynomial σ R))).comp
      (MvPolynomial.C (σ := σ)))
    ((IsFractionRing.injective (MvPolynomial σ R) (FractionRing (MvPolynomial σ R))).comp
      (MvPolynomial.C_injective σ R))
  exact Algebra.isTranscendentalSeparable_of_perfectField _ _

end MvPowerSeries
