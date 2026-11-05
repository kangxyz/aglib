/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Original normalization maps of injective domain arrows

The native fraction-field lift and its original square transport integrality.
No finiteness or normality of either original domain is assumed.
-/

@[expose] public noncomputable section
namespace integralClosure
universe u v
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] (f : A →+* B) (hf : Function.Injective f)

/-- The actual extension to the two original fraction fields. -/
def fractionMapOfInjective : FractionRing A →+* FractionRing B :=
  IsFractionRing.lift (g := (algebraMap B (FractionRing B)).comp f)
    ((IsFractionRing.injective B (FractionRing B)).comp hf)

@[simp]
theorem fractionMapOfInjective_algebraMap (a : A) :
    fractionMapOfInjective f hf (algebraMap A (FractionRing A) a) =
      algebraMap B (FractionRing B) (f a) :=
  IsFractionRing.lift_algebraMap (g := (algebraMap B (FractionRing B)).comp f)
    ((IsFractionRing.injective B (FractionRing B)).comp hf) a

/-- The original field injection restricted to the two literal normalizations. -/
def mapOfInjective : integralClosure A (FractionRing A) →+*
    integralClosure B (FractionRing B) where
  toFun x := ⟨fractionMapOfInjective f hf x,
    IsIntegral.map_of_comp_eq f (fractionMapOfInjective f hf)
      (by ext a; exact (fractionMapOfInjective_algebraMap f hf a).symm)
      ((mem_integralClosure_iff A (FractionRing A)).mp x.property)⟩
  map_zero' := Subtype.ext (map_zero (fractionMapOfInjective f hf))
  map_one' := Subtype.ext (map_one (fractionMapOfInjective f hf))
  map_add' x y := Subtype.ext (map_add (fractionMapOfInjective f hf) x.val y.val)
  map_mul' x y := Subtype.ext (map_mul (fractionMapOfInjective f hf) x.val y.val)

/-- The coefficient square is the original arrow, not an abstract comparison. -/
theorem mapOfInjective_algebraMap :
    (mapOfInjective f hf).comp (algebraMap A (integralClosure A (FractionRing A))) =
      (algebraMap B (integralClosure B (FractionRing B))).comp f := by
  ext a
  exact fractionMapOfInjective_algebraMap f hf a

/-- The induced normalization map is genuinely injective. -/
theorem mapOfInjective_injective : Function.Injective (mapOfInjective f hf) := by
  intro x y h
  apply Subtype.ext
  exact (fractionMapOfInjective f hf).injective (congrArg Subtype.val h)

end integralClosure
