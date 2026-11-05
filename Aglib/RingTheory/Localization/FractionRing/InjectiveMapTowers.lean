/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.InjectiveNormalizationMap

/-! # The original fraction-field towers of any injective domain arrow

The canonical extension of the supplied ring map supplies compatible algebra
structures on the two original fraction fields. Scalar actions are fixed to
those of these exact algebra maps; no alternative Ore-localization action is
selected. No normality, finiteness or normalization presentation is required.
-/

@[expose] public noncomputable section

namespace integralClosure

universe u v

/-- Both original fraction-field towers of the given injective arrow, with
all scalar dictionaries fixed to the displayed structural algebra maps. -/
theorem fractionMapOfInjective_towers
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] (f : R →+* S) (hf : Function.Injective f) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R (FractionRing S) :=
      ((algebraMap S (FractionRing S)).comp f).toAlgebra
    letI : Algebra (FractionRing R) (FractionRing S) :=
      (fractionMapOfInjective f hf).toAlgebra
    letI : SMul R S := Algebra.toSMul
    letI : SMul R (FractionRing R) := Algebra.toSMul
    letI : SMul S (FractionRing S) := Algebra.toSMul
    letI : SMul R (FractionRing S) := Algebra.toSMul
    letI : SMul (FractionRing R) (FractionRing S) := Algebra.toSMul
    IsScalarTower R S (FractionRing S) ∧
      IsScalarTower R (FractionRing R) (FractionRing S) := by
  let : Algebra R S := f.toAlgebra
  let : Algebra R (FractionRing S) :=
    ((algebraMap S (FractionRing S)).comp f).toAlgebra
  let : Algebra (FractionRing R) (FractionRing S) :=
    (fractionMapOfInjective f hf).toAlgebra
  let : SMul R S := Algebra.toSMul
  let : SMul R (FractionRing R) := Algebra.toSMul
  let : SMul S (FractionRing S) := Algebra.toSMul
  let : SMul R (FractionRing S) := Algebra.toSMul
  let : SMul (FractionRing R) (FractionRing S) := Algebra.toSMul
  constructor
  · exact IsScalarTower.of_algebraMap_eq'
      (R := R) (S := S) (A := FractionRing S) rfl
  · apply IsScalarTower.of_algebraMap_eq
      (R := R) (S := FractionRing R) (A := FractionRing S)
    intro x
    exact (fractionMapOfInjective_algebraMap f hf x).symm

end integralClosure
