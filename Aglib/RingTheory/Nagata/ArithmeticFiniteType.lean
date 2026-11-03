/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.Arithmetic
public import Aglib.RingTheory.Nagata.FiniteType
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Arithmetic finite-type normalization in the original universe

Only the integer coefficient ring is lifted to the universe of the original
algebra. Its ring equivalence supplies the original arithmetic properties.
The target algebra, its fraction field and literal normalization are unchanged.
-/

@[expose] public noncomputable section

universe u

private theorem ulift_int_nagata : IsNagataRing.{u, 0} (ULift.{u} ℤ) := by
  let D := ULift.{u} ℤ
  let e : D ≃+* ℤ := ULift.ringEquiv
  let : IsDomain D := e.toMulEquiv.isDomain ℤ
  let : IsNoetherianRing D := isNoetherianRing_of_ringEquiv ℤ e.symm
  let : IsIntegrallyClosed D := IsIntegrallyClosed.of_equiv e.symm
  let : Ring.DimensionLEOne D := Ring.DimensionLEOne.of_ringEquiv e
  let : CharZero D := ⟨fun m n h ↦ Int.ofNat_inj.mp (congrArg ULift.down h)⟩
  let : IsDedekindDomain D := { }
  exact IsNagataRing.of_isDedekindDomain_charZero D

/-- Any integer finite-type algebra is Nagata in its own universe. Only the
coefficient ring is lifted; the original algebra and integer map are retained. -/
theorem IsNagataRing.of_finiteType_int
    (A : Type u) [CommRing A] [Algebra.FiniteType ℤ A] : IsNagataRing.{u, 0} A := by
  let D := ULift.{u} ℤ
  let : Algebra D A := ((algebraMap ℤ A).comp ULift.ringEquiv.toRingHom).toAlgebra
  let := IsScalarTower.of_algebraMap_eq'
    (R := ℤ) (S := D) (A := A) (Subsingleton.elim _ _)
  let : Algebra.FiniteType D A := Algebra.FiniteType.of_restrictScalars_finiteType ℤ D A
  exact (ulift_int_nagata.{u}).of_finiteType

/-- Finite type over the original `ℤ[1/n]` gives Nagata without inverting any
additional integer and without restricting the target algebra's universe. -/
theorem IsNagataRing.of_finiteType_int_away
    (n : ℤ) (A : Type u) [CommRing A]
    [Algebra (Localization.Away n) A] [Algebra.FiniteType (Localization.Away n) A] :
    IsNagataRing.{u, 0} A := by
  let := IsScalarTower.of_algebraMap_eq'
    (R := ℤ) (S := Localization.Away n) (A := A) (Subsingleton.elim _ _)
  let : Algebra.FiniteType ℤ A := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType ℤ (Localization.Away n))
    (inferInstance : Algebra.FiniteType (Localization.Away n) A)
  exact IsNagataRing.of_finiteType_int A

/-- Literal normalization of an arithmetic finite-type domain in any supplied
same-universe finite extension of its original fraction field is finite. -/
theorem integralClosure.finite_of_finiteType_int_away
    (n : ℤ) (A K L : Type u) [CommRing A] [IsDomain A]
    [Algebra (Localization.Away n) A] [Algebra.FiniteType (Localization.Away n) A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] : Module.Finite A (integralClosure A L) :=
  IsJapaneseRing.finite_integralClosure_of_isFractionRing
    (IsNagataRing.of_finiteType_int_away n A).isJapaneseRing K L

/-- In particular, the initial arithmetic domain has finite literal
normalization in its own original fraction field, without a normality premise. -/
theorem integralClosure.finite_fractionRing_of_finiteType_int_away
    (n : ℤ) (A : Type u) [CommRing A] [IsDomain A]
    [Algebra (Localization.Away n) A] [Algebra.FiniteType (Localization.Away n) A] :
    Module.Finite A (integralClosure A (FractionRing A)) :=
  finite_of_finiteType_int_away n A (FractionRing A) (FractionRing A)
