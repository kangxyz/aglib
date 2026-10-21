/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedMapPresentation
public import Aglib.Algebra.Category.ModuleCat.KernelBaseChange

/-! # The original scalar-extension square for graded presentations -/

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

/-- The original coefficient map commutes with the native scalar-extension presentation. -/
theorem formalGradedAffinePresentation_map_square :
    letI := formalGradedSectionAlgebra f U
    letI : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
    letI : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
    letI := formalGradedAffineModule f I F U
    letI := formalGradedAffineModule f I G U
    (formalGradedAffineMap f I U φ).comp (formalGradedAffinePresentation f I F U) =
      (formalGradedAffinePresentation f I G U).comp
        (LinearMap.baseChange (R := ↑(X.presheaf.obj (op U)))
          (M := Γ(F.gradedPiece 0, U)) (N := Γ(G.gradedPiece 0, U))
          (Γ(X, U) ⊗[A] I.associatedGraded) ((F.gradedPieceMap φ 0).val.app (op U)).hom) := by
  let := formalGradedSectionAlgebra f U
  let : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
  let : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
  let := formalGradedAffineModule f I F U
  let := formalGradedAffineModule f I G U
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul c y => exact formalGradedAffineMap_presentation_tmul f I U φ c y
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The same original square in categorical scalar-extension coordinates. -/
theorem formalGradedAffinePresentation_map_square_categorical :
    letI := formalGradedSectionAlgebra f U
    letI : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
    letI : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
    letI := formalGradedAffineModule f I F U
    letI := formalGradedAffineModule f I G U
    ModuleCat.ofHom (formalGradedAffinePresentation f I F U) ≫
        ModuleCat.ofHom (formalGradedAffineMap f I U φ) =
      (ModuleCat.extendScalarsAlgebraIso Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded)
        ((F.gradedPiece 0).val.obj (op U))).inv ≫
      (ModuleCat.extendScalars (algebraMap Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded))).map
        ((F.gradedPieceMap φ 0).val.app (op U)) ≫
      (ModuleCat.extendScalarsAlgebraIso Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded)
        ((G.gradedPiece 0).val.obj (op U))).hom ≫
      ModuleCat.ofHom (formalGradedAffinePresentation f I G U) := by
  let := formalGradedSectionAlgebra f U
  let : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
  let : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
  let := formalGradedAffineModule f I F U
  let := formalGradedAffineModule f I G U
  have hq : ModuleCat.ofHom (formalGradedAffinePresentation f I F U) ≫
        ModuleCat.ofHom (formalGradedAffineMap f I U φ) =
      ModuleCat.ofHom (LinearMap.baseChange (R := ↑(X.presheaf.obj (op U)))
        (M := Γ(F.gradedPiece 0, U)) (N := Γ(G.gradedPiece 0, U))
        (Γ(X, U) ⊗[A] I.associatedGraded) ((F.gradedPieceMap φ 0).val.app (op U)).hom) ≫
        ModuleCat.ofHom (formalGradedAffinePresentation f I G U) := by
    apply ModuleCat.hom_ext
    exact formalGradedAffinePresentation_map_square f I U φ
  rw [hq]
  have hc := ModuleCat.extendScalarsAlgebraIso_naturality Γ(X, U)
    (Γ(X, U) ⊗[A] I.associatedGraded) ((F.gradedPieceMap φ 0).val.app (op U))
  apply (cancel_epi
    (ModuleCat.extendScalarsAlgebraIso Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded)
      ((F.gradedPiece 0).val.obj (op U))).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ ModuleCat.ofHom (formalGradedAffinePresentation f I G U))
      hc.symm).trans (Category.assoc _ _ _))

end AlgebraicGeometry.Scheme.Cohomology
