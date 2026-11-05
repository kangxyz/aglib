/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.OrdinaryMate
public import Aglib.CategoryTheory.Adjunction.Mates.ChartBoundary

/-! # Restriction normalization of the original composite-chart mate

The original inverse-image chart isomorphisms cancel using naturality of the
original direct-image square. No sheafification model is changed.
-/
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

/-- Both original chart boundaries cancel before native component evaluation. -/
theorem sourceEtaleCompositeDirectIso_app_normalized (U : X.Etale)
    (F : AbelianSheaf.{u, u + 1} X') : type_of% (
  congrArg (fun z => z.app F) (SourceChartMates.rightIso_normalize
    (inverseImageEtaleIso U.hom)
    (inverseImageEtaleIso ((siteBaseChange g').obj U).hom)
    (etaleDirectImageRestrictionIso g' U.hom)
    (directImageSquareIso (U.hom ≫ f) (pullback.snd U.hom g' ≫ f') g
      (pullback.fst U.hom g') (sourceEtaleCompositeSquare f f' g g' H U).w.symm)
    (sourceEtaleImageRestrictionIso f U)
    (sourceEtaleImageRestrictionIso f' ((siteBaseChange g').obj U)))
    ) :=
  congrArg (fun z => z.app F) (SourceChartMates.rightIso_normalize
    (inverseImageEtaleIso U.hom)
    (inverseImageEtaleIso ((siteBaseChange g').obj U).hom)
    (etaleDirectImageRestrictionIso g' U.hom)
    (directImageSquareIso (U.hom ≫ f) (pullback.snd U.hom g' ≫ f') g
      (pullback.fst U.hom g') (sourceEtaleCompositeSquare f f' g g' H U).w.symm)
    (sourceEtaleImageRestrictionIso f U)
    (sourceEtaleImageRestrictionIso f' ((siteBaseChange g').obj U)))

end AlgebraicGeometry.Scheme.EtaleCohomology
