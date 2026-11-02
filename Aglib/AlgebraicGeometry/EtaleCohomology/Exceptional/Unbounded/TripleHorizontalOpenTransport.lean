/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperOpenCongruence
public import Aglib.AlgebraicGeometry.Compactification.Refinements.TripleCompositionSquares
public import Aglib.AlgebraicGeometry.Compactification.Refinements.TripleCompositionFirst

/-! # The original horizontal mate along the actual middle-open factorization -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wY wF wM wT
variable {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
  [QuasiCompact g] [QuasiCompact h] (T : Hom.TripleCompactifiedComposition f g h)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wF} (ModuleSheaf T.leftInner.first.Xbar Λ)]
  [hM : HasDerivedCategory.{wM} (ModuleSheaf T.middle.Xbar Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T.first.Xbar Λ)]

/-- The local derived-category model on `ModuleSheaf T.tail.sourceCompactification.Xbar Λ`. -/
local instance unboundedTripleHorizontalTransportLocal1 : HasDerivedCategory.{wM}
    (ModuleSheaf T.tail.sourceCompactification.Xbar Λ) := hM

/-- This is equality transport of the actual open arrow, not a new horizontal exchange. -/
theorem moduleUnboundedTripleHorizontalOpenTransport :
    moduleUnboundedProperOpenMate T.leftInner.first.p (T.leftInner.middleOpen ≫ T.innerToFirst)
      (T.tail.first.j ≫ T.tail.middleOpen) T.first.p
      (T.leftInner.isPullback_middleOpen.flip.paste_vert T.isPullback_innerToFirst) Λ =
      Functor.whiskerLeft (moduleUnboundedDerivedDirectImage Λ T.leftInner.first.p)
        (eqToHom (moduleUnboundedDerivedLowerShriek_congr Λ T.tail.first_j_middleOpen)) ≫
      moduleUnboundedProperOpenMate T.leftInner.first.p (T.leftInner.middleOpen ≫ T.innerToFirst)
        T.tail.sourceCompactification.j T.first.p T.isPullback_first.flip Λ := by
  simpa only [eqToHom_refl, Functor.whiskerRight_id', Category.comp_id] using
    (moduleUnboundedProperOpenMate_congr_opens Λ T.tail.first_j_middleOpen
      (rfl : T.leftInner.middleOpen ≫ T.innerToFirst =
        T.leftInner.middleOpen ≫ T.innerToFirst)
      T.leftInner.first.p T.first.p
      (T.leftInner.isPullback_middleOpen.flip.paste_vert T.isPullback_innerToFirst)
      T.isPullback_first.flip)

end AlgebraicGeometry.Scheme.EtaleCohomology
