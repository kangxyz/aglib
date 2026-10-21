/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedAffineScalars
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedNaturality

/-! # Original tensor-linear maps of formal graded affine modules -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite DirectSum GradedMonoid
open scoped TensorProduct
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I)) (U : X.Opens)

variable {F G : AdicSystem X (idealThickeningIdealSheaf f I)} (φ : F ⟶ G)

/-- The original componentwise map, retaining the coordinate scalars. -/
def formalGradedAffineCoordinateMap :
    (⨁ n, Γ(F.gradedPiece n, U)) →ₗ[Γ(X, U)] (⨁ n, Γ(G.gradedPiece n, U)) :=
  DirectSum.lmap (fun n => ((F.gradedPieceMap φ n).val.app (op U)).hom)

@[simp]
theorem formalGradedAffineCoordinateMap_of (n : ℕ) (x : Γ(F.gradedPiece n, U)) :
    formalGradedAffineCoordinateMap f I U φ
      (DirectSum.of (fun k => Γ(F.gradedPiece k, U)) n x) =
      DirectSum.of (fun k => Γ(G.gradedPiece k, U)) n ((F.gradedPieceMap φ n).app U x) := by
  exact DirectSum.lmap_of (fun k => ((F.gradedPieceMap φ k).val.app (op U)).hom) n x

/-- The actual componentwise map is linear over the full tensor ring. -/
def formalGradedAffineMap :
    letI := formalGradedSectionAlgebra f U
    letI : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
    letI : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
    letI := formalGradedAffineModule f I F U
    letI := formalGradedAffineModule f I G U
    (⨁ n, Γ(F.gradedPiece n, U)) →ₗ[Γ(X, U) ⊗[A] I.associatedGraded]
      (⨁ n, Γ(G.gradedPiece n, U)) := by
  letI := formalGradedSectionAlgebra f U
  letI : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
  letI : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
  letI := formalGradedAffineModule f I F U
  letI := formalGradedAffineModule f I G U
  refine { toFun := formalGradedAffineCoordinateMap f I U φ
           map_add' := (formalGradedAffineCoordinateMap f I U φ).map_add
           map_smul' := ?_ }
  intro c x
  change formalGradedAffineCoordinateMap f I U φ (c • x) =
    c • formalGradedAffineCoordinateMap f I U φ x
  induction c using TensorProduct.inductionOn with
  | tmul b s =>
    induction s using DirectSum.Decomposition.inductionOn I.associatedGradedGrading with
    | zero => simp only [TensorProduct.tmul_zero, zero_smul, map_zero]
    | homogeneous a =>
      induction x using DirectSum.induction_on with
      | zero => simp only [smul_zero, map_zero]
      | of n x =>
        rw [formalGradedAffineModule_tmul_component_smul,
          formalGradedAffineCoordinateMap_of, formalGradedAffineCoordinateMap_of,
          formalGradedAffineModule_tmul_component_smul]
        apply congrArg (DirectSum.of (fun k => Γ(G.gradedPiece k, U)) (_ + n))
        change ((F.gradedPieceMap φ _).val.app (op U)).hom
          (b • (formalGradedHomogeneousAction f I F _ n a).app U x) = _
        rw [_root_.map_smul]
        apply congrArg (b • ·)
        exact (congrArg (fun k => k.app U x)
          (formalGradedHomogeneousAction_naturality f I φ _ n a)).symm
      | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | add s t hs ht => simp only [TensorProduct.tmul_add, add_smul, map_add, hs, ht]
  | add s t hs ht => simp only [add_smul, map_add, hs, ht]

@[simp]
theorem formalGradedAffineMap_of (n : ℕ) (x : Γ(F.gradedPiece n, U)) :
    formalGradedAffineMap f I U φ
      (DirectSum.of (fun k => Γ(F.gradedPiece k, U)) n x) =
      DirectSum.of (fun k => Γ(G.gradedPiece k, U)) n ((F.gradedPieceMap φ n).app U x) :=
  formalGradedAffineCoordinateMap_of f I U φ n x

end AlgebraicGeometry.Scheme.Cohomology
