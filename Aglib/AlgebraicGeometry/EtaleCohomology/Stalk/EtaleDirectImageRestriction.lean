/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleRestrictionUnit
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

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
  NatIso.ofComponents
    (fun U => MorphismProperty.Over.isoMk (pullbackRightPullbackFstIso g f U.hom)
      (pullbackRightPullbackFstIso_hom_snd g f U.hom))
    (fun {U V} a => by
      apply MorphismProperty.Over.Hom.ext
      change pullback.lift (pullback.fst U.hom (pullback.fst g f) ≫ a.left)
          (pullback.snd U.hom (pullback.fst g f)) _ ≫
            (pullbackRightPullbackFstIso g f V.hom).hom =
        (pullbackRightPullbackFstIso g f U.hom).hom ≫
          pullback.lift (pullback.fst (U.hom ≫ g) f ≫ a.left)
            (pullback.snd (U.hom ≫ g) f) _
      apply pullback.hom_ext
      · simp only [Category.assoc, pullbackRightPullbackFstIso_hom_fst,
          pullback.lift_fst, pullbackRightPullbackFstIso_hom_fst_assoc]
      · simp only [Category.assoc, pullbackRightPullbackFstIso_hom_snd,
          pullback.lift_snd_assoc, pullback.lift_snd])

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
