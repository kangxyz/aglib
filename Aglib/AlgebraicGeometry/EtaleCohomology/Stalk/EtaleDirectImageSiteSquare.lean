/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleDirectImageRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap

/-! # Native test-scheme square and chart-adjunction counits -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

/-- The native comparison of iterated base changes for a commuting scheme square. -/
def siteBaseChangeSquareIso {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) :
    siteBaseChange g ⋙ siteBaseChange f' ≅ siteBaseChange f ⋙ siteBaseChange g' :=
  (siteBaseChangeComp g f').symm ≪≫
    eqToIso (congrArg (fun k : X' ⟶ S => siteBaseChange k) h) ≪≫
      siteBaseChangeComp f g'

/-- Forgetting the whole native square gives the same actual Over square. -/
theorem siteBaseChangeSquareIso_forget {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) :
    Functor.whiskerRight (siteBaseChangeSquareIso f f' g g' h).hom
        (Scheme.Etale.forget X') =
      Functor.whiskerLeft (Scheme.Etale.forget S)
        (Over.pullbackSquareIso f f' g g' h).hom :=
  MorphismProperty.Over.forget_pullbackSquareIso_hom @Etale f f' g g' h

/-- The actual square comparison preserves projection to the original test object. -/
theorem siteBaseChangeSquareIso_fst_fst {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (U : S.Etale) :
    ((siteBaseChangeSquareIso f f' g g' h).hom.app U).left ≫
        pullback.fst (pullback.snd U.hom f) g' ≫ pullback.fst U.hom f =
      pullback.fst (pullback.snd U.hom g) f' ≫ pullback.fst U.hom g :=
  MorphismProperty.Over.pullbackSquareIso_fst_fst @Etale f f' g g' h U

/-- The pasted chart comparison respects the two original site counits. -/
theorem siteEtaleDirectImageRestriction_counit {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) [Etale g] (U : S.Etale) :
    (siteEtalePostcompose (pullback.snd g f)).map
        ((siteBaseChangeSquareIso f (pullback.fst g f) g (pullback.snd g f)
          pullback.condition).hom.app U) ≫
        (siteEtalePostcomposeAdj (pullback.snd g f)).counit.app ((siteBaseChange f).obj U) =
      (siteEtaleDirectImageRestrictionIso f g).hom.app ((siteBaseChange g).obj U) ≫
        (siteBaseChange f).map ((siteEtalePostcomposeAdj g).counit.app U) :=
  MorphismProperty.Over.pullbackPostcomposeIso_counit_app @Etale f g inferInstance U

end AlgebraicGeometry.Scheme.EtaleCohomology
