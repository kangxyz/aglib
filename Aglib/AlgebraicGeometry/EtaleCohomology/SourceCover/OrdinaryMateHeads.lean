/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.OrdinaryMateNormalization

/-! # Exact original chart heads before ordinary mate normalization -/
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

/-- The original right-square formula uses exactly the normalization boundary
word. Only literal pulled-back chart projection heads are aligned. -/
theorem sourceEtaleCompositeDirectIso_normalization_head (U : X.Etale) :
    sourceEtaleCompositeDirectIso f f' g g' H U =
      SourceChartMates.rightIso
        (Functor.isoWhiskerLeft (directImage g') (inverseImageEtaleIso U.hom) ≪≫
          etaleDirectImageRestrictionIso g' U.hom ≪≫
          Functor.isoWhiskerRight
            (inverseImageEtaleIso ((siteBaseChange g').obj U).hom).symm
            (directImage (pullback.fst U.hom g')))
        (directImageSquareIso (U.hom ≫ f) (pullback.snd U.hom g' ≫ f') g
          (pullback.fst U.hom g') (sourceEtaleCompositeSquare f f' g g' H U).w.symm)
        (sourceEtaleImageRestrictionIso f U ≪≫
          Functor.isoWhiskerRight (inverseImageEtaleIso U.hom).symm (directImage (U.hom ≫ f)))
        (sourceEtaleImageRestrictionIso f' ((siteBaseChange g').obj U) ≪≫
          Functor.isoWhiskerRight
            (inverseImageEtaleIso ((siteBaseChange g').obj U).hom).symm
            (directImage (pullback.snd U.hom g' ≫ f'))) := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
