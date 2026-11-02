/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionTripleInterchange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.TripleOpenContraction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.DirectImageContraction
public import Aglib.CategoryTheory.Functor.ImageTripleCompositionPredicate
public import Aglib.AlgebraicGeometry.Compactification.Refinements.TripleCompositionSquares

/-! # Actual triple-tower interchange associativity

All three Cartesian squares are the literal open restrictions of the supplied
three-level tower. No geometric compatibility or map coherence is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wW wA₀ wA₁ wA₂ wB₀ wB₁ wY wZ wC
variable {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
  [QuasiCompact g] [QuasiCompact h] (T : Hom.TripleCompactifiedComposition f g h)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wW} (ModuleSheaf W Λ)]
  [HasDerivedCategory.{wA₀} (ModuleSheaf T.leftInner.first.Xbar Λ)]
  [HasDerivedCategory.{wA₁} (ModuleSheaf T.leftInner.sourceCompactification.Xbar Λ)]
  [HasDerivedCategory.{wA₂} (ModuleSheaf T.first.Xbar Λ)]
  [HasDerivedCategory.{wB₀} (ModuleSheaf T.tail.first.Xbar Λ)]
  [middleModel : HasDerivedCategory.{wB₁} (ModuleSheaf T.middle.Xbar Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf T.last.Xbar Λ)]

/-- The local derived-category model on `ModuleSheaf T.tail.sourceCompactification.Xbar Λ`. -/
local instance unboundedTripleRawCompositionModel : HasDerivedCategory.{wB₁}
    (ModuleSheaf T.tail.sourceCompactification.Xbar Λ) := middleModel

/-- The actual raw binary-map routes of the triple tower agree with original compositors. -/
theorem moduleUnboundedTripleRawCompositionEquation :
    ImageTripleCompositionEquation
      (moduleUnboundedProperOpenMate T.leftInner.first.p T.leftInner.middleOpen T.tail.first.j
        T.leftInner.sourceCompactification.p T.leftInner.isPullback_middleOpen.flip Λ)
      (moduleUnboundedProperOpenMate T.tail.first.p T.tail.middleOpen T.last.j T.middle.p
        T.tail.isPullback_middleOpen.flip Λ)
      (moduleUnboundedProperOpenMate (T.leftInner.sourceCompactification.p ≫ T.tail.first.p)
        T.innerToFirst T.last.j (T.first.p ≫ T.middle.p) (T.isPullback_innerToFirst.paste_horiz
        T.tail.isPullback_middleOpen.flip) Λ)
      (moduleUnboundedProperOpenMate T.leftInner.first.p (T.leftInner.middleOpen ≫
        T.innerToFirst) (T.tail.first.j ≫ T.tail.middleOpen) T.first.p
        (T.leftInner.isPullback_middleOpen.flip.paste_vert T.isPullback_innerToFirst) Λ)
      (moduleUnboundedDerivedDirectImageCompIso Λ T.tail.first.p
        T.leftInner.sourceCompactification.p)
      (moduleUnboundedDerivedLowerShriekCompIso Λ T.tail.middleOpen T.tail.first.j)
      (moduleUnboundedDerivedLowerShriekOverIso Λ T.leftInner.first.j T.leftInner.middleOpen
        T.leftInner.sourceCompactification.j T.leftInner.first_j_middleOpen)
      (moduleUnboundedDerivedLowerShriekOverIso Λ T.leftInner.sourceCompactification.j
        T.innerToFirst
        T.first.j T.leftInner_j_innerToFirst)
      (moduleUnboundedDerivedLowerShriekOverIso Λ T.leftInner.first.j
        (T.leftInner.middleOpen ≫ T.innerToFirst) T.first.j (unboundedTripleFirstOpenEquality T))
      (moduleUnboundedDerivedDirectImageCompIso Λ T.last.p (T.first.p ≫ T.middle.p)).symm
      (moduleUnboundedDerivedDirectImageCompIso Λ T.last.p T.middle.p).symm
      ((moduleUnboundedDerivedDirectImageCompIso Λ (T.middle.p ≫ T.last.p) T.first.p).symm ≪≫
        eqToIso (congrArg (fun q : T.first.Xbar ⟶ W => moduleUnboundedDerivedDirectImage Λ q)
          (Category.assoc T.first.p T.middle.p T.last.p).symm)) := by
  exact imageTripleCompositionEquation _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (moduleUnboundedTripleCompactifiedInterchangeAssociativity T Λ)
    (moduleUnboundedTripleOpenContraction T Λ)
    (moduleUnboundedDerivedDirectImageContraction_assoc Λ T.first.p T.middle.p T.last.p)

end AlgebraicGeometry.Scheme.EtaleCohomology
