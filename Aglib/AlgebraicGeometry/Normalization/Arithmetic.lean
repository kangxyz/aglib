/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.FunctionField
public import Aglib.RingTheory.Nagata.ArithmeticFiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Finiteness of the original arithmetic generic normalization

Actual affine chart maps of the original locally finite-type arithmetic model
supply finite-type integer algebras. Their derived Nagata property proves that
the unchanged generic-normalization projection is finite. No external Nagata
or normalization-finiteness certificate and no replacement scheme is required.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

/-- The original generic normalization of an integral scheme locally of finite
type over an integer finite-type affine base is finite. -/
theorem genericNormalization_isFinite_of_finiteType_int
    (A : CommRingCat.{u}) [Algebra.FiniteType ℤ A]
    (W : Scheme.{u}) [IsIntegral W] (f : W ⟶ Spec A) [LocallyOfFiniteType f] :
    IsFinite (W.fromSpecStalk (genericPoint W)).fromNormalization := by
  apply genericNormalization_isFinite W
  intro U _
  let φ : A →+* Γ(W, U.1) :=
    (f.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso A).inv.hom
  have hφ : φ.FiniteType :=
    (f.finiteType_appLE (isAffineOpen_top _) U.2 le_top).comp
      (RingHom.FiniteType.of_surjective (Scheme.ΓSpecIso A).inv.hom
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).2)
  let : Algebra A Γ(W, U.1) := φ.toAlgebra
  let : Algebra.FiniteType A Γ(W, U.1) := hφ
  let := IsScalarTower.of_algebraMap_eq'
    (R := ℤ) (S := A) (A := Γ(W, U.1)) (Subsingleton.elim _ _)
  let : Algebra.FiniteType ℤ Γ(W, U.1) := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType ℤ A)
    (inferInstance : Algebra.FiniteType A Γ(W, U.1))
  exact IsNagataRing.of_finiteType_int Γ(W, U.1)

/-- Arithmetic models over the original `ℤ[1/n]` retain their original scheme,
function field, generic inclusion and normalization projection. -/
theorem genericNormalization_isFinite_of_finiteType_int_away
    (n : ℤ) (A : CommRingCat.{u})
    [Algebra (Localization.Away n) A] [Algebra.FiniteType (Localization.Away n) A]
    (W : Scheme.{u}) [IsIntegral W] (f : W ⟶ Spec A) [LocallyOfFiniteType f] :
    IsFinite (W.fromSpecStalk (genericPoint W)).fromNormalization := by
  let := IsScalarTower.of_algebraMap_eq'
    (R := ℤ) (S := Localization.Away n) (A := A) (Subsingleton.elim _ _)
  let : Algebra.FiniteType ℤ A := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType ℤ (Localization.Away n))
    (inferInstance : Algebra.FiniteType (Localization.Away n) A)
  exact genericNormalization_isFinite_of_finiteType_int A W f

/-- The actual initial affine arithmetic domain has finite generic normalization,
without any normality assumption on that domain. -/
theorem genericNormalization_isFinite_spec_int_away
    (n : ℤ) (A : CommRingCat.{u}) [IsDomain A]
    [Algebra (Localization.Away n) A] [Algebra.FiniteType (Localization.Away n) A] :
    IsFinite ((Spec A).fromSpecStalk (genericPoint (Spec A))).fromNormalization :=
  genericNormalization_isFinite_of_finiteType_int_away n A (Spec A) (𝟙 _)

end AlgebraicGeometry.Scheme
