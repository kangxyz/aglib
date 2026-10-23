/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.FiniteEtale

/-!
# Finite normalization over an integral model of a normal base

If `S` is integral over `R`, its integral closure in the same ambient algebra
has the same elements as the integral closure of `R`. The comparison is the
identity in that ambient algebra. When `R` is normal Noetherian and the
ambient generic algebra is finite etale, the actual normalization of `S`
is finite over both `R` and `S`; normality of `S` is not required.
-/

@[expose] public noncomputable section

namespace integralClosure

section IntegralModel

variable (R S A : Type*) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
  [Algebra.IsIntegral R S]

/-- Integral change of the coefficient ring does not change the elements of
the actual integral closure in the specified ambient algebra. -/
def equivOfIntegral : integralClosure S A ≃ₐ[R] integralClosure R A where
  toFun x := ⟨x.1, isIntegral_trans (R := R) x.1 x.2⟩
  invFun x := ⟨x.1, x.2.tower_top⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The comparison retains the exact element in the original ambient algebra. -/
@[simp] theorem coe_equivOfIntegral (x : integralClosure S A) :
    (equivOfIntegral R S A x : A) = (x : A) := rfl

/-- The inverse comparison also retains the original element. -/
@[simp] theorem coe_equivOfIntegral_symm (x : integralClosure R A) :
    ((equivOfIntegral R S A).symm x : A) = (x : A) := rfl

end IntegralModel

section Finiteness

variable (R K S A : Type*) [CommRing R] [IsDomain R]
  [IsIntegrallyClosed R] [IsNoetherianRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [Algebra S A] [IsScalarTower R S A] [Algebra.Etale K A]

include R K

/-- The normalization of an integral model is finite over the original
normal Noetherian base for a finite etale generic algebra. -/
theorem finite_base_of_integral_of_etale : Module.Finite R (integralClosure S A) := by
  let : Module.Finite R (integralClosure R A) := finite_of_etale R K A
  exact Module.Finite.equiv (equivOfIntegral R S A).symm.toLinearEquiv

/-- The same literal normalization is finite over the possibly nonnormal
integral model, with its original structural map. -/
theorem finite_of_integral_of_etale : Module.Finite S (integralClosure S A) := by
  let : Module.Finite R (integralClosure S A) := finite_base_of_integral_of_etale R K S A
  exact Module.Finite.of_restrictScalars_finite R S _

end Finiteness

section SeparableField

variable (R K S L : Type*) [CommRing R] [IsDomain R]
  [IsIntegrallyClosed R] [IsNoetherianRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra S L] [IsScalarTower R S L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

include R K

/-- The field version uses the existing trace-dual finiteness theorem;
the normalization is that of the actual, possibly nonnormal, model `S`. -/
theorem finite_of_integral_of_isSeparable : Module.Finite S (integralClosure S L) := by
  let : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L _
  let : Module.Finite R (integralClosure S L) :=
    Module.Finite.equiv (equivOfIntegral R S L).symm.toLinearEquiv
  exact Module.Finite.of_restrictScalars_finite R S _

end SeparableField

end integralClosure
