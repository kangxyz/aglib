/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationGraded
public import Aglib.AlgebraicGeometry.Modules.KernelSections
public import Aglib.LinearAlgebra.DirectSum.Kernels

/-! # Original direct sums of relation graded sections are actual graded-map kernels -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite DirectSum
namespace AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X] {K : X.IdealSheafData}
  {P F : AdicSystem X K} (φ : P ⟶ F) (U : X.Opens)

/-- Original affine coordinates of the actual relation graded-piece kernel.
The section comparison itself works on every open. -/
def relationGradedSectionsKernelEquiv (n : ℕ) :
    Γ(relationGradedPiece φ n, U) ≃ₗ[Γ(X, U)]
      ((P.gradedPieceMap φ n).val.app (op U)).hom.ker :=
  (show ModuleCat.of Γ(X, U) Γ(relationGradedPiece φ n, U) ≅
      ModuleCat.of Γ(X, U) ((P.gradedPieceMap φ n).val.app (op U)).hom.ker from
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).mapIso
      (relationGradedPieceIso φ n) ≪≫ kernelSectionsIso (P.gradedPieceMap φ n) U).toLinearEquiv

@[simp]
theorem relationGradedSectionsKernelEquiv_apply (n : ℕ)
    (x : Γ(relationGradedPiece φ n, U)) :
    (relationGradedSectionsKernelEquiv φ U n x).val =
      ((relationGradedPieceIso φ n).hom ≫ kernel.ι (P.gradedPieceMap φ n)).app U x := by
  change (kernelSectionsLinearEquiv (P.gradedPieceMap φ n) U
    ((relationGradedPieceIso φ n).hom.app U x)).val = _
  rw [kernelSectionsLinearEquiv_apply]
  rfl

/-- Native direct sums of the original adjacent relation kernels identify with
the kernel of the original componentwise graded coefficient map. -/
def relationGradedTotalKernelEquiv :
    (⨁ n, Γ(relationGradedPiece φ n, U)) ≃ₗ[Γ(X, U)]
      (DirectSum.lmap (fun n => ((P.gradedPieceMap φ n).val.app (op U)).hom)).ker :=
  (DirectSum.congrLinearEquiv (R := Γ(X, U)) (relationGradedSectionsKernelEquiv φ U)).trans
    (DirectSum.kernelLmapEquiv (R := Γ(X, U))
      (fun n => ((P.gradedPieceMap φ n).val.app (op U)).hom))

/-- The total equivalence retains each original inclusion into the coefficient total. -/
@[simp]
theorem relationGradedTotalKernelEquiv_apply_component
    (x : ⨁ n, Γ(relationGradedPiece φ n, U)) (n : ℕ) :
    (relationGradedTotalKernelEquiv φ U x).val n =
      ((relationGradedPieceIso φ n).hom ≫ kernel.ι (P.gradedPieceMap φ n)).app U (x n) := by
  change (relationGradedSectionsKernelEquiv φ U n (x n)).val = _
  exact relationGradedSectionsKernelEquiv_apply φ U n (x n)

end AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
