/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.DirectImage
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Truncation.AtZero

/-!
# The degree-zero truncation of actual derived direct image

The comparison uses native homology normalization and the original direct-image
functor. No vanishing hypothesis on positive higher images is required.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry DerivedCategory.Plus

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u dS dX

variable {S X : Scheme.{u}}
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]

/-- The actual truncation below one of Rf_* applied to a degree-zero sheaf is
canonically the single of the original f_* sheaf. -/
def derivedDirectImageTruncLTOneIso (f : S ⟶ X)
    (L : AbelianSheaf.{u, u + 1} S) :
    (TStructure.t.truncLT 1).obj
        ((derivedDirectImage f).obj
          ((singleFunctor (AbelianSheaf.{u, u + 1} S) 0).obj L)) ≅
      (singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj ((directImage f).obj L) := by
  exact (directImage f).rightDerivedFunctorPlusTruncLTOneIso L

/-- The actual direct-image comparison retains the original truncation arrow,
native higher-image comparison and original right-derived-zero normalization. -/
@[reassoc]
theorem derivedDirectImageTruncLTOneIso_homology_zero (f : S ⟶ X)
    (L : AbelianSheaf.{u, u + 1} S) :
    (homologyFunctor (AbelianSheaf.{u, u + 1} X) 0).map
        (derivedDirectImageTruncLTOneIso f L).hom ≫
      (singleFunctorCompHomologyFunctorIso (C := AbelianSheaf.{u, u + 1} X) 0).hom.app
        ((directImage f).obj L) =
    (homologyFunctor (AbelianSheaf.{u, u + 1} X) 0).map ((TStructure.t.truncLTι 1).app
        ((derivedDirectImage f).obj
          ((singleFunctor (AbelianSheaf.{u, u + 1} S) 0).obj L))) ≫
      (higherDirectImageIso f 0).inv.app L ≫ (directImage f).rightDerivedZeroIsoSelf.hom.app L :=
  (directImage f).rightDerivedFunctorPlusTruncLTOneIso_homology_zero L

end AlgebraicGeometry.Scheme.EtaleCohomology
