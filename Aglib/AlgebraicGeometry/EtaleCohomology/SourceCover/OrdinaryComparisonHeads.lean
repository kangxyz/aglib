/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.OrdinaryFaces
public import Aglib.CategoryTheory.Adjunction.Mates.ComparisonEvaluation

/-! # Preserve the complete original comparison value before evaluation -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge
variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (H : IsPullback g' f' f g)

/-- Only the complete original natural transformation is unfolded. -/
theorem sourceEtaleOrdinaryComparison_as_generic (U : X.Etale) :
    sourceEtaleOrdinaryComparison f f' g g' H U =
      SourceChartMates.comparison
        (inverseImageSquareIso U.hom ((siteBaseChange g').obj U).hom g'
          (pullback.fst U.hom g') pullback.condition.symm).symm
        (baseChangeMap (U.hom ≫ f) (pullback.snd U.hom g' ≫ f') g
          (pullback.fst U.hom g') (sourceEtaleCompositeSquare f f' g g' H U).w.symm)
        (sourceEtaleImageInverseIso f U)
        (sourceEtaleImageInverseIso f' ((siteBaseChange g').obj U)) := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
