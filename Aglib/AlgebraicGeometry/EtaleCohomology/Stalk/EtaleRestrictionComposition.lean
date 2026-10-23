/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleRestrictionUnit
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackCoherence

/-! # The original composition of étale chart restriction -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) [Etale f] [Etale g]

/-- Postcomposition of original test schemes, with the native associativity iso. -/
def siteEtalePostcomposeComp :
    siteEtalePostcompose (g ≫ f) ≅ siteEtalePostcompose g ⋙ siteEtalePostcompose f :=
  MorphismProperty.Over.mapComp (P := @Etale) (Q := ⊤)
    (show Etale g from inferInstance) (show Etale f from inferInstance)

/-- Restriction composition is induced by the original postcomposition iso. -/
def etaleRestrictionComp :
    etaleRestriction (g ≫ f) ≅ etaleRestriction f ⋙ etaleRestriction g :=
  (Functor.sheafPushforwardContinuousComp' (siteEtalePostcomposeComp f g).symm
    AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology T)
    (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X)).symm

/-- The original site counits compose through the actual iterated pullback. -/
theorem siteEtalePostcomposeComp_counit (U : X.Etale) :
    (siteEtalePostcomposeComp f g).hom.app ((siteBaseChange (g ≫ f)).obj U) ≫
        (siteEtalePostcompose f).map
          ((siteEtalePostcompose g).map ((siteBaseChangeComp f g).hom.app U)) ≫
        (siteEtalePostcompose f).map
          ((siteEtalePostcomposeAdj g).counit.app ((siteBaseChange f).obj U)) ≫
        (siteEtalePostcomposeAdj f).counit.app U =
      (siteEtalePostcomposeAdj (g ≫ f)).counit.app U := by
  apply MorphismProperty.Over.Hom.ext
  change 𝟙 _ ≫ ((siteBaseChangeComp f g).hom.app U).left ≫
      pullback.fst (pullback.snd U.hom f) g ≫ pullback.fst U.hom f =
    pullback.fst U.hom (g ≫ f)
  exact (Category.id_comp _).trans
    (MorphismProperty.Over.pullbackComp_left_fst_fst
      (P := @Etale) (Q := ⊤) g f U)

end AlgebraicGeometry.Scheme.EtaleCohomology
