/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenComposition
public import Aglib.AlgebraicGeometry.Compactification.Refinements.TripleCompositionSquares

/-! # The actual three-open contraction in the genuine triple compactification -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wA wB wC
variable {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
  [QuasiCompact g] [QuasiCompact h] (T : Hom.TripleCompactifiedComposition f g h)
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hA : HasDerivedCategory.{wA} (ModuleSheaf T.leftInner.first.Xbar Λ)]
  [hB : HasDerivedCategory.{wB} (ModuleSheaf T.leftInner.sourceCompactification.Xbar Λ)]
  [hC : HasDerivedCategory.{wC} (ModuleSheaf T.first.Xbar Λ)]

/-- The source equality for the actual iterated original open restriction. -/
theorem unboundedTripleFirstOpenEquality :
    T.leftInner.first.j ≫ (T.leftInner.middleOpen ≫ T.innerToFirst) = T.first.j :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ T.innerToFirst) T.leftInner.first_j_middleOpen).trans
      T.leftInner_j_innerToFirst)

/-- No replacement source map occurs in the triple open-compositor face. -/
theorem moduleUnboundedTripleOpenContraction :
    OpenCompositionEquation
      (moduleUnboundedDerivedLowerShriekOverIso Λ T.leftInner.first.j T.leftInner.middleOpen
        T.leftInner.sourceCompactification.j T.leftInner.first_j_middleOpen)
      (moduleUnboundedDerivedLowerShriekOverIso Λ T.leftInner.sourceCompactification.j
        T.innerToFirst
        T.first.j T.leftInner_j_innerToFirst)
      (moduleUnboundedDerivedLowerShriekOverIso Λ T.leftInner.first.j
        (T.leftInner.middleOpen ≫ T.innerToFirst) T.first.j (unboundedTripleFirstOpenEquality T))
      (moduleUnboundedDerivedLowerShriekCompIso Λ T.innerToFirst T.leftInner.middleOpen).symm :=
  moduleUnboundedDerivedLowerShriekOverIso_assoc Λ T.leftInner.first.j T.leftInner.middleOpen
    T.innerToFirst T.leftInner.sourceCompactification.j T.first.j
    T.leftInner.first_j_middleOpen T.leftInner_j_innerToFirst

end AlgebraicGeometry.Scheme.EtaleCohomology
