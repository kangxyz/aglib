/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleRestrictionUnit
public import Aglib.CategoryTheory.Over.SitePullbackPasting

/-! # Original direct image restricted to an étale chart -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) [Etale g]

/-- The actual test schemes in étale chart base change are the pasted pullbacks. -/
def siteEtaleDirectImageRestrictionIso :
    siteBaseChange (pullback.fst g f) ⋙ siteEtalePostcompose (pullback.snd g f) ≅
      siteEtalePostcompose g ⋙ siteBaseChange f :=
  MorphismProperty.Over.pullbackPostcomposeIso @Etale f g inferInstance

/-- The entire native comparison is the restriction of the same Over comparison. -/
theorem siteEtaleDirectImageRestrictionIso_forget :
    Functor.whiskerRight (siteEtaleDirectImageRestrictionIso f g).hom
        (Scheme.Etale.forget X) =
      Functor.whiskerLeft (Scheme.Etale.forget T) (Over.pullbackPostcomposeIso f g).hom :=
  MorphismProperty.Over.forget_pullbackPostcomposeIso_hom @Etale f g inferInstance

/-- Restriction preserves the literal pasted-pullback component. -/
theorem siteEtaleDirectImageRestrictionIso_hom_left (U : T.Etale) :
    ((siteEtaleDirectImageRestrictionIso f g).hom.app U).left =
      (pullbackRightPullbackFstIso g f U.hom).hom := rfl

/-- Actual sheaf restriction of direct image is direct image on the actual pullback chart.
The isomorphism is natural in the original coefficient sheaf. -/
def etaleDirectImageRestrictionIso :
    directImage f ⋙ etaleRestriction g ≅
      etaleRestriction (pullback.snd g f) ⋙ directImage (pullback.fst g f) := by
  let : (siteEtalePostcompose g ⋙ siteBaseChange f).IsContinuous
      (Scheme.smallEtaleTopology T) (Scheme.smallEtaleTopology X) :=
    Functor.isContinuous_comp _ _ (Scheme.smallEtaleTopology T)
      (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X)
  let : (siteBaseChange (pullback.fst g f) ⋙
      siteEtalePostcompose (pullback.snd g f)).IsContinuous
      (Scheme.smallEtaleTopology T) (Scheme.smallEtaleTopology X) :=
    Functor.isContinuous_comp _ _ (Scheme.smallEtaleTopology T)
      (Scheme.smallEtaleTopology (pullback g f)) (Scheme.smallEtaleTopology X)
  exact Functor.sheafPushforwardContinuousIso (siteEtaleDirectImageRestrictionIso f g).symm
    AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology T) (Scheme.smallEtaleTopology X)

end AlgebraicGeometry.Scheme.EtaleCohomology
