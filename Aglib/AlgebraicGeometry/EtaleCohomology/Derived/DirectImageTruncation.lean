/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.DirectImage
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Layers
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure

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
  let K := (derivedDirectImage f).obj
    ((singleFunctor (AbelianSheaf.{u, u + 1} S) 0).obj L)
  let : K.IsGE 0 := (directImage f).rightDerivedFunctorPlus_isGE _ 0
  let : ((TStructure.t.truncLT 1).obj K).IsLE 0 :=
    TStructure.t.isLE_truncLT_obj K 1 0 (by omega)
  exact isoSingleHomology ((TStructure.t.truncLT 1).obj K) 0 ≪≫
    (singleFunctor (AbelianSheaf.{u, u + 1} X) 0).mapIso
      (homologyTruncLTIso K 1 0 (by omega) ≪≫
        (derivedDirectImageSingleHomologyZeroIso f).app L)

end AlgebraicGeometry.Scheme.EtaleCohomology
