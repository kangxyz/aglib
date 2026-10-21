/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedAffineScalars
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedTensorNaturality
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.DirectSumOpenRestriction
public import Aglib.RingTheory.AssociatedGraded.TensorRing
public import Aglib.RingTheory.AssociatedGraded.NativeRing
public import Aglib.RingTheory.TensorProduct.CoordinatePushout
public import Aglib.RingTheory.AssociatedGraded.CoordinateModuleBijective

/-! # Full tensor base change of original formal graded sections -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite DirectSum GradedMonoid
open scoped TensorProduct ChangeOfRings
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))

variable (U V : X.affineOpens) (i : V.val ⟶ U.val)

/-- Original restriction viewed as a linear map over the source tensor algebra. -/
def formalGradedTensorRestrictionLinear :
    letI := formalGradedSectionAlgebra f U.val
    letI := formalGradedSectionAlgebra f V.val
    letI : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
    letI : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
    letI : Semiring (Γ(X, V) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, V)) (B := I.associatedGraded)
    letI : NonAssocSemiring (Γ(X, V) ⊗[A] I.associatedGraded) :=
      (inferInstance : Semiring (Γ(X, V) ⊗[A] I.associatedGraded)).toNonAssocSemiring
    letI : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map i.op).hom.toAlgebra
    letI : IsScalarTower A Γ(X, U) Γ(X, V) :=
      IsScalarTower.of_algebraMap_eq fun a =>
        ((formalGradedCoordinateRestriction f (leOfHom i)).commutes a).symm
    letI : Algebra (Γ(X, U) ⊗[A] I.associatedGraded)
        (Γ(X, V) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.coordinateAlgebra A Γ(X, U) Γ(X, V) I.associatedGraded
    letI := formalGradedAffineModule f I F U.val
    letI := formalGradedAffineModule f I F V.val
    letI : Module (Γ(X, U) ⊗[A] I.associatedGraded)
        (⨁ n, Γ(F.gradedPiece n, V)) :=
      Module.compHom (R := Γ(X, V) ⊗[A] I.associatedGraded)
        (S := Γ(X, U) ⊗[A] I.associatedGraded)
        (⨁ n, Γ(F.gradedPiece n, V))
        (algebraMap (Γ(X, U) ⊗[A] I.associatedGraded) (Γ(X, V) ⊗[A] I.associatedGraded))
    (⨁ n, Γ(F.gradedPiece n, U)) →ₗ[Γ(X, U) ⊗[A] I.associatedGraded]
      (⨁ n, Γ(F.gradedPiece n, V)) := by
  letI := formalGradedSectionAlgebra f U.val
  letI := formalGradedSectionAlgebra f V.val
  letI : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
  letI : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
  letI : Semiring (Γ(X, V) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, V)) (B := I.associatedGraded)
  letI : NonAssocSemiring (Γ(X, V) ⊗[A] I.associatedGraded) :=
    (inferInstance : Semiring (Γ(X, V) ⊗[A] I.associatedGraded)).toNonAssocSemiring
  letI : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map i.op).hom.toAlgebra
  letI : IsScalarTower A Γ(X, U) Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      ((formalGradedCoordinateRestriction f (leOfHom i)).commutes a).symm
  letI : Algebra (Γ(X, U) ⊗[A] I.associatedGraded)
      (Γ(X, V) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.coordinateAlgebra A Γ(X, U) Γ(X, V) I.associatedGraded
  letI := formalGradedAffineModule f I F U.val
  letI := formalGradedAffineModule f I F V.val
  letI : Module (Γ(X, U) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, V)) :=
    Module.compHom (R := Γ(X, V) ⊗[A] I.associatedGraded)
      (S := Γ(X, U) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, V))
      (algebraMap (Γ(X, U) ⊗[A] I.associatedGraded) (Γ(X, V) ⊗[A] I.associatedGraded))
  exact {
    toFun := formalGradedSectionsRestriction f I F (leOfHom i)
    map_add' := (formalGradedSectionsRestriction f I F (leOfHom i)).map_add
    map_smul' t x := formalGradedSectionsRestriction_tensor_smul f I F (leOfHom i) t x
  }

/-- The original coordinate unit agrees with the original tensor-linear restriction. -/
theorem formalGradedTensorRestrictionLinear_unit_component (n : ℕ)
    (x : Γ(F.gradedPiece n, U)) :
    (directSumAffineOpenRestrictionIso U V i F.gradedPiece).hom
      ((1 : Γ(X, V)) ⊗ₜ[Γ(X, U),(X.presheaf.map i.op).hom]
        DirectSum.lof Γ(X, U) ℕ (fun k => Γ(F.gradedPiece k, U)) n x) =
      formalGradedTensorRestrictionLinear f I F U V i
        (DirectSum.of (fun k => Γ(F.gradedPiece k, U)) n x) := by
  have hr : formalGradedTensorRestrictionLinear f I F U V i
      (DirectSum.of (fun k => Γ(F.gradedPiece k, U)) n x) =
      DirectSum.of (fun k => Γ(F.gradedPiece k, V)) n
        ((F.gradedPiece n).val.map i.op x) :=
    formalGradedSectionsRestriction_of f I F (leOfHom i) n x
  exact (directSumAffineOpenRestrictionIso_one_tmul_lof U V i F.gradedPiece n x).trans hr.symm

/-- Bijectivity of the original scalar-extension map is checked before packaging the equivalence. -/
theorem formalGradedTensorRestriction_bijective :
    letI := formalGradedSectionAlgebra f U.val
    letI := formalGradedSectionAlgebra f V.val
    letI : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
    letI : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
    letI : Semiring (Γ(X, V) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, V)) (B := I.associatedGraded)
    letI : NonAssocSemiring (Γ(X, V) ⊗[A] I.associatedGraded) :=
      (inferInstance : Semiring (Γ(X, V) ⊗[A] I.associatedGraded)).toNonAssocSemiring
    letI : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map i.op).hom.toAlgebra
    letI : IsScalarTower A Γ(X, U) Γ(X, V) :=
      IsScalarTower.of_algebraMap_eq fun a =>
        ((formalGradedCoordinateRestriction f (leOfHom i)).commutes a).symm
    letI : Algebra (Γ(X, U) ⊗[A] I.associatedGraded)
        (Γ(X, V) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.coordinateAlgebra A Γ(X, U) Γ(X, V) I.associatedGraded
    letI := formalGradedAffineModule f I F U.val
    letI := formalGradedAffineModule f I F V.val
    letI : Module (Γ(X, U) ⊗[A] I.associatedGraded)
        (⨁ n, Γ(F.gradedPiece n, V)) :=
      Module.compHom (R := Γ(X, V) ⊗[A] I.associatedGraded)
        (S := Γ(X, U) ⊗[A] I.associatedGraded)
        (⨁ n, Γ(F.gradedPiece n, V))
        (algebraMap (Γ(X, U) ⊗[A] I.associatedGraded) (Γ(X, V) ⊗[A] I.associatedGraded))
    letI : IsScalarTower (Γ(X, U) ⊗[A] I.associatedGraded)
        (Γ(X, V) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, V)) :=
      IsScalarTower.of_compHom _ _ _
    Function.Bijective
      ((formalGradedTensorRestrictionLinear f I F U V i).liftBaseChange
        (Γ(X, V) ⊗[A] I.associatedGraded)) := by
  let := formalGradedSectionAlgebra f U.val
  let := formalGradedSectionAlgebra f V.val
  let : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
  let : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
  let : Semiring (Γ(X, V) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, V)) (B := I.associatedGraded)
  let : NonAssocSemiring (Γ(X, V) ⊗[A] I.associatedGraded) :=
    (inferInstance : Semiring (Γ(X, V) ⊗[A] I.associatedGraded)).toNonAssocSemiring
  let : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map i.op).hom.toAlgebra
  let : IsScalarTower A Γ(X, U) Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      ((formalGradedCoordinateRestriction f (leOfHom i)).commutes a).symm
  let : Algebra (Γ(X, U) ⊗[A] I.associatedGraded)
      (Γ(X, V) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.coordinateAlgebra A Γ(X, U) Γ(X, V) I.associatedGraded
  let hRing : IsScalarTower Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded)
      (Γ(X, V) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.coordinateAlgebra_tower A Γ(X, U) Γ(X, V) I.associatedGraded
  let : Algebra.IsPushout Γ(X, U) Γ(X, V)
      (Γ(X, U) ⊗[A] I.associatedGraded) (Γ(X, V) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.coordinateAlgebra_isPushout A Γ(X, U) Γ(X, V) I.associatedGraded
  let mCU := formalGradedAffineModule (A := A) (X := X) f I F U.val
  let mCV := formalGradedAffineModule (A := A) (X := X) f I F V.val
  let hCU : IsScalarTower Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, U)) :=
    formalGradedAffineModule_scalarTower_left f I F U.val
  let hCV : IsScalarTower Γ(X, V) (Γ(X, V) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, V)) :=
    formalGradedAffineModule_scalarTower_left f I F V.val
  let : Module (Γ(X, U) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, V)) :=
    Module.compHom (R := Γ(X, V) ⊗[A] I.associatedGraded)
      (S := Γ(X, U) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, V))
      (algebraMap (Γ(X, U) ⊗[A] I.associatedGraded) (Γ(X, V) ⊗[A] I.associatedGraded))
  let : IsScalarTower (Γ(X, U) ⊗[A] I.associatedGraded)
      (Γ(X, V) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, V)) :=
    IsScalarTower.of_compHom _ _ _
  let e : Γ(X, V) ⊗[Γ(X, U)] (⨁ n, Γ(F.gradedPiece n, U)) ≃ₗ[Γ(X, V)]
      (⨁ n, Γ(F.gradedPiece n, V)) :=
    (directSumAffineOpenRestrictionIso U V i F.gradedPiece).toLinearEquiv
  let r : (⨁ n, Γ(F.gradedPiece n, U)) →ₗ[Γ(X, U) ⊗[A] I.associatedGraded]
      (⨁ n, Γ(F.gradedPiece n, V)) := formalGradedTensorRestrictionLinear f I F U V i
  let : CommRing I.associatedGraded := I.associatedGradedCommRing
  have hg := I.associatedGradedCoordinateLiftBaseChange_bijective_of_directSum Γ(X, U) Γ(X, V)
    (N := ⨁ n, Γ(F.gradedPiece n, V)) (fun n => Γ(F.gradedPiece n, U))
    (mCP := mCU) (mE := mCV) (hCP := hCU) (hE := hCV)
  apply hg r e
  intro n x
  exact formalGradedTensorRestrictionLinear_unit_component f I F U V i n x

/-- Localization on affine opens is base change over the full tensor-coordinate ring. -/
def formalGradedTensorRestrictionEquiv :
    letI := formalGradedSectionAlgebra f U.val
    letI := formalGradedSectionAlgebra f V.val
    letI : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
    letI : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
    letI : Semiring (Γ(X, V) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, V)) (B := I.associatedGraded)
    letI : NonAssocSemiring (Γ(X, V) ⊗[A] I.associatedGraded) :=
      (inferInstance : Semiring (Γ(X, V) ⊗[A] I.associatedGraded)).toNonAssocSemiring
    letI : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map i.op).hom.toAlgebra
    letI : IsScalarTower A Γ(X, U) Γ(X, V) :=
      IsScalarTower.of_algebraMap_eq fun a =>
        ((formalGradedCoordinateRestriction f (leOfHom i)).commutes a).symm
    letI : Algebra (Γ(X, U) ⊗[A] I.associatedGraded)
        (Γ(X, V) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.coordinateAlgebra A Γ(X, U) Γ(X, V) I.associatedGraded
    letI := formalGradedAffineModule f I F U.val
    letI := formalGradedAffineModule f I F V.val
    (Γ(X, V) ⊗[A] I.associatedGraded) ⊗[Γ(X, U) ⊗[A] I.associatedGraded]
      (⨁ n, Γ(F.gradedPiece n, U)) ≃ₗ[Γ(X, V) ⊗[A] I.associatedGraded]
        (⨁ n, Γ(F.gradedPiece n, V)) := by
  letI := formalGradedSectionAlgebra f U.val
  letI := formalGradedSectionAlgebra f V.val
  letI : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
  letI : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
  letI : Semiring (Γ(X, V) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, V)) (B := I.associatedGraded)
  letI : NonAssocSemiring (Γ(X, V) ⊗[A] I.associatedGraded) :=
    (inferInstance : Semiring (Γ(X, V) ⊗[A] I.associatedGraded)).toNonAssocSemiring
  letI : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map i.op).hom.toAlgebra
  letI : IsScalarTower A Γ(X, U) Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      ((formalGradedCoordinateRestriction f (leOfHom i)).commutes a).symm
  letI : Algebra (Γ(X, U) ⊗[A] I.associatedGraded)
      (Γ(X, V) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.coordinateAlgebra A Γ(X, U) Γ(X, V) I.associatedGraded
  letI := formalGradedAffineModule f I F U.val
  letI := formalGradedAffineModule f I F V.val
  letI : Module (Γ(X, U) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, V)) :=
    Module.compHom (R := Γ(X, V) ⊗[A] I.associatedGraded)
      (S := Γ(X, U) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, V))
      (algebraMap (Γ(X, U) ⊗[A] I.associatedGraded) (Γ(X, V) ⊗[A] I.associatedGraded))
  letI : IsScalarTower (Γ(X, U) ⊗[A] I.associatedGraded)
      (Γ(X, V) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, V)) :=
    IsScalarTower.of_compHom _ _ _
  exact LinearEquiv.ofBijective
    ((formalGradedTensorRestrictionLinear f I F U V i).liftBaseChange
      (Γ(X, V) ⊗[A] I.associatedGraded))
    (formalGradedTensorRestriction_bijective f I F U V i)

/-- The full tensor comparison preserves each original homogeneous restriction. -/
theorem formalGradedTensorRestrictionEquiv_one_tmul_of (n : ℕ)
    (x : Γ(F.gradedPiece n, U)) :
    letI := formalGradedSectionAlgebra f U.val
    letI := formalGradedSectionAlgebra f V.val
    letI : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
    letI : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
    letI : Semiring (Γ(X, V) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, V)) (B := I.associatedGraded)
    letI : NonAssocSemiring (Γ(X, V) ⊗[A] I.associatedGraded) :=
      (inferInstance : Semiring (Γ(X, V) ⊗[A] I.associatedGraded)).toNonAssocSemiring
    letI : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map i.op).hom.toAlgebra
    letI : IsScalarTower A Γ(X, U) Γ(X, V) :=
      IsScalarTower.of_algebraMap_eq fun a =>
        ((formalGradedCoordinateRestriction f (leOfHom i)).commutes a).symm
    letI : Algebra (Γ(X, U) ⊗[A] I.associatedGraded)
        (Γ(X, V) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.coordinateAlgebra A Γ(X, U) Γ(X, V) I.associatedGraded
    letI := formalGradedAffineModule f I F U.val
    letI := formalGradedAffineModule f I F V.val
    formalGradedTensorRestrictionEquiv f I F U V i
      (1 ⊗ₜ[Γ(X, U) ⊗[A] I.associatedGraded]
        DirectSum.of (fun k => Γ(F.gradedPiece k, U)) n x) =
      DirectSum.of (fun k => Γ(F.gradedPiece k, V)) n
        ((F.gradedPiece n).val.map i.op x) := by
  let := formalGradedSectionAlgebra f U.val
  let := formalGradedSectionAlgebra f V.val
  let : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
  let : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
  let : Semiring (Γ(X, V) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, V)) (B := I.associatedGraded)
  let : NonAssocSemiring (Γ(X, V) ⊗[A] I.associatedGraded) :=
    (inferInstance : Semiring (Γ(X, V) ⊗[A] I.associatedGraded)).toNonAssocSemiring
  let : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map i.op).hom.toAlgebra
  let : IsScalarTower A Γ(X, U) Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      ((formalGradedCoordinateRestriction f (leOfHom i)).commutes a).symm
  let : Algebra (Γ(X, U) ⊗[A] I.associatedGraded)
      (Γ(X, V) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.coordinateAlgebra A Γ(X, U) Γ(X, V) I.associatedGraded
  let : IsScalarTower Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded)
      (Γ(X, V) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.coordinateAlgebra_tower A Γ(X, U) Γ(X, V) I.associatedGraded
  let : Algebra.IsPushout Γ(X, U) Γ(X, V)
      (Γ(X, U) ⊗[A] I.associatedGraded) (Γ(X, V) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.coordinateAlgebra_isPushout A Γ(X, U) Γ(X, V) I.associatedGraded
  let := formalGradedAffineModule f I F U.val
  let := formalGradedAffineModule f I F V.val
  let : IsScalarTower Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, U)) :=
    formalGradedAffineModule_scalarTower_left f I F U.val
  let : IsScalarTower Γ(X, V) (Γ(X, V) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, V)) :=
    formalGradedAffineModule_scalarTower_left f I F V.val
  let : Module (Γ(X, U) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, V)) :=
    Module.compHom (R := Γ(X, V) ⊗[A] I.associatedGraded)
      (S := Γ(X, U) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, V))
      (algebraMap (Γ(X, U) ⊗[A] I.associatedGraded) (Γ(X, V) ⊗[A] I.associatedGraded))
  let : IsScalarTower (Γ(X, U) ⊗[A] I.associatedGraded)
      (Γ(X, V) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, V)) :=
    IsScalarTower.of_compHom _ _ _
  change (1 : Γ(X, V) ⊗[A] I.associatedGraded) •
    formalGradedTensorRestrictionLinear f I F U V i
      (DirectSum.of (fun k => Γ(F.gradedPiece k, U)) n x) = _
  rw [one_smul]
  exact formalGradedSectionsRestriction_of f I F (leOfHom i) n x

end AlgebraicGeometry.Scheme.Cohomology
