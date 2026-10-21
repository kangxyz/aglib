/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationTower
public import Aglib.CategoryTheory.Abelian.KernelSquareExact

/-! # Original graded kernels of the ordinary relation tower -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem

universe u

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {K : X.IdealSheafData}
  {P F : AdicSystem X K} (φ : P ⟶ F)

/-- The ordinary successive kernel of the relation tower. -/
abbrev relationGradedPiece (n : ℕ) : X.Modules := kernel (relationTransition φ n)

/-- The actual successive relation kernel is the kernel of the original map
on successive pieces. No cartesian property of the relation tower is used. -/
def relationGradedPieceIso (n : ℕ) :
    relationGradedPiece φ n ≅ kernel (P.gradedPieceMap φ n) :=
  CategoryTheory.Abelian.kernelSquareIso
    (φ.hom.app (op (n + 1))) (φ.hom.app (op n))
    (P.transition n) (F.transition n) (P.transition_naturality φ n).symm

/-- The comparison keeps the original double kernel inclusion into `P_(n+1)`. -/
@[reassoc (attr := simp)]
theorem relationGradedPieceIso_hom_ι_ι (n : ℕ) :
    (relationGradedPieceIso φ n).hom ≫
        kernel.ι (P.gradedPieceMap φ n) ≫ kernel.ι (P.transition n) =
      kernel.ι (relationTransition φ n) ≫ kernel.ι (φ.hom.app (op (n + 1))) :=
  CategoryTheory.Abelian.kernelSquareIso_hom_ι_ι _ _ _ _ _

/-- Levelwise epimorphisms induce epimorphisms on the original successive
pieces. The correction uses surjective ordinary relation transitions. -/
instance gradedPieceMap_epi (n : ℕ) [Epi (φ.hom.app (op (n + 1)))] :
    Epi (P.gradedPieceMap φ n) := by
  have : Epi (kernel.map (φ.hom.app (op (n + 1))) (φ.hom.app (op n))
      (P.transition n) (F.transition n) (P.transition_naturality φ n).symm) :=
    relationTransition_epi φ n
  exact CategoryTheory.Abelian.epi_kernel_map_of_epi_of_epi_kernel_map
    (φ.hom.app (op (n + 1))) (φ.hom.app (op n))
    (P.transition n) (F.transition n) (P.transition_naturality φ n).symm

end AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
