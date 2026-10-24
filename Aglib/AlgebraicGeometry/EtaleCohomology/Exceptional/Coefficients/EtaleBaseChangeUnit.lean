/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.EtaleBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleDirectImageSiteSquare
public import Aglib.CategoryTheory.Adjunction.ExchangeRestriction

/-!
# Original unit compatibility for module-valued étale exchange

The coefficient-free square of test schemes induces the direct-image square
with module coefficients. Its compatibility with the actual site counits
identifies the original chart exchange with the original inverse-image units.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

/-- The direct-image square induced by the original square of test schemes. -/
def moduleValuedDirectImageSquareIso {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (Λ : Type (u + 1)) [Ring Λ] :
    moduleValuedDirectImage g' Λ ⋙ moduleValuedDirectImage f Λ ≅
      moduleValuedDirectImage f' Λ ⋙ moduleValuedDirectImage g Λ := by
  let : (siteBaseChange f ⋙ siteBaseChange g').IsContinuous
      (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X') :=
    Functor.isContinuous_comp _ _ (Scheme.smallEtaleTopology S)
      (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology X')
  let : (siteBaseChange g ⋙ siteBaseChange f').IsContinuous
      (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X') :=
    Functor.isContinuous_comp _ _ (Scheme.smallEtaleTopology S)
      (Scheme.smallEtaleTopology S') (Scheme.smallEtaleTopology X')
  exact Functor.sheafPushforwardContinuousIso (siteBaseChangeSquareIso f f' g g' h).symm
    (ModuleCat.{u + 1} Λ) (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X')

/-- On sections, the direct-image square is the actual test-scheme square. -/
theorem moduleValuedDirectImageSquareIso_hom_app {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (Λ : Type (u + 1)) [Ring Λ]
    (F : ModuleValuedSheaf X' Λ) (U : S.Etale) :
    ((moduleValuedDirectImageSquareIso f f' g g' h Λ).hom.app F).hom.app (op U) =
      F.obj.map ((siteBaseChangeSquareIso f f' g g' h).hom.app U).op := rfl

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) [Etale g]
  (Λ : Type (u + 1)) [Ring Λ]

/-- The restriction exchange respects the original site-adjunction units. -/
theorem moduleValuedEtaleRestriction_directImage_unit (F : ModuleValuedSheaf X Λ) :
    (moduleValuedEtaleRestrictionAdjunction g Λ).unit.app
        ((moduleValuedDirectImage f Λ).obj F) ≫
      (moduleValuedDirectImage g Λ).map
        ((moduleValuedEtaleDirectImageRestrictionIso f g Λ).hom.app F) =
    (moduleValuedDirectImage f Λ).map
        ((moduleValuedEtaleRestrictionAdjunction (pullback.snd g f) Λ).unit.app F) ≫
      (moduleValuedDirectImageSquareIso f (pullback.fst g f) g (pullback.snd g f)
        pullback.condition Λ).hom.app
          ((moduleValuedEtaleRestriction (pullback.snd g f) Λ).obj F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change F.obj.map ((siteBaseChange f).map
      ((siteEtalePostcomposeAdj g).counit.app U.unop)).op ≫
      F.obj.map ((siteEtaleDirectImageRestrictionIso f g).hom.app
        ((siteBaseChange g).obj U.unop)).op =
    F.obj.map ((siteEtalePostcomposeAdj (pullback.snd g f)).counit.app
      ((siteBaseChange f).obj U.unop)).op ≫
    F.obj.map ((siteEtalePostcompose (pullback.snd g f)).map
      ((siteBaseChangeSquareIso f (pullback.fst g f) g (pullback.snd g f)
        pullback.condition).hom.app U.unop)).op
  exact ((F.obj.map_comp _ _).symm).trans
    ((congrArg (fun a => F.obj.map a.op)
      (siteEtaleDirectImageRestriction_counit f g U.unop).symm).trans
      (F.obj.map_comp _ _))

/-- The actual module-valued chart exchange respects the original inverse-image units. -/
theorem moduleValuedEtaleBaseChangeIso_unit (F : ModuleValuedSheaf X Λ) :
    (moduleValuedDirectImage f Λ).map
        ((moduleValuedInverseImageAdjunction (pullback.snd g f) Λ).unit.app F) ≫
      (moduleValuedDirectImageSquareIso f (pullback.fst g f) g (pullback.snd g f)
        pullback.condition Λ).hom.app
          ((moduleValuedInverseImage (pullback.snd g f) Λ).obj F) =
    (moduleValuedInverseImageAdjunction g Λ).unit.app
        ((moduleValuedDirectImage f Λ).obj F) ≫
      (moduleValuedDirectImage g Λ).map
        ((moduleValuedEtaleBaseChangeIso f g Λ).hom.app F) := by
  exact Adjunction.exchangeRestriction_unit
    (moduleValuedDirectImage f Λ) (moduleValuedDirectImage (pullback.fst g f) Λ)
    (moduleValuedInverseImageAdjunction (pullback.snd g f) Λ)
    (moduleValuedInverseImageAdjunction g Λ)
    (moduleValuedEtaleRestrictionAdjunction (pullback.snd g f) Λ)
    (moduleValuedEtaleRestrictionAdjunction g Λ)
    (moduleValuedInverseImageEtaleIso (pullback.snd g f) Λ)
    (moduleValuedInverseImageEtaleIso g Λ)
    (moduleValuedEtaleDirectImageRestrictionIso f g Λ)
    (moduleValuedDirectImageSquareIso f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition Λ).hom
    (moduleValuedInverseImageEtaleIso_unit (pullback.snd g f) Λ)
    (moduleValuedInverseImageEtaleIso_unit g Λ)
    (moduleValuedEtaleRestriction_directImage_unit f g Λ) F

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
