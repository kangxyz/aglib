/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleDirectImageSiteSquare
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeHorizontalUnit
public import Aglib.CategoryTheory.Adjunction.Mates.OriginalExchange

/-! # The ordinary étale chart isomorphism is the original exchange mate -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.OriginalExchange


universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

local instance {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) :
    (siteBaseChange f ⋙ siteBaseChange g).IsContinuous
      (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology T) :=
  Functor.isContinuous_comp (siteBaseChange f) (siteBaseChange g)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)
    (Scheme.smallEtaleTopology T)

private theorem directImageCompIso_hom_transform {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) :
    (directImageCompIso f g).hom =
      Functor.sheafPushforwardContinuousNatTrans (siteBaseChangeComp f g).hom
        AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology X)
        (Scheme.smallEtaleTopology T) := by
  exact Category.id_comp _

private theorem directImageCompIso_inv_transform {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) :
    (directImageCompIso f g).inv =
      Functor.sheafPushforwardContinuousNatTrans (siteBaseChangeComp f g).inv
        AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology X)
        (Scheme.smallEtaleTopology T) := by
  exact Category.comp_id _

private theorem directImage_eqToIso_transform {X S : Scheme.{u}} {f g : S ⟶ X}
    (h : f = g) :
    (eqToIso (congrArg (fun k => directImage k) h)).hom =
      Functor.sheafPushforwardContinuousNatTrans
        (eqToHom (congrArg (fun k => siteBaseChange k) h.symm))
        AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology X)
        (Scheme.smallEtaleTopology S) := by
  subst g
  apply NatTrans.ext
  funext F
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change (𝟙 _) = F.obj.map (𝟙 _)
  exact (F.obj.map_id _).symm

private theorem directImageSquareIso_transform {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) :
    (directImageSquareIso f f' g g' h).hom =
      Functor.sheafPushforwardContinuousNatTrans
        (siteBaseChangeSquareIso f f' g g' h).hom AddCommGrpCat.{u + 1}
        (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X') := by
  refine (iso_chain_hom_of_eq (directImageCompIso f g')
    (eqToIso (congrArg (fun k => directImage k) h.symm))
    (directImageCompIso g f').symm _ _ _
    (directImageCompIso_hom_transform f g') (directImage_eqToIso_transform h.symm)
    (directImageCompIso_inv_transform g f')).trans ?_
  exact continuous_three_transforms (A := AddCommGrpCat.{u + 1})
    (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X')
    (siteBaseChangeComp g f').inv
    (eqToHom (congrArg (fun k => siteBaseChange k) h)) (siteBaseChangeComp f g').hom

private theorem directImageSquareIso_app_hom {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (F : AbelianSheaf.{u, u + 1} X') (U : S.Etale) :
    ((directImageSquareIso f f' g g' h).hom.app F).hom.app (op U) =
      F.obj.map ((siteBaseChangeSquareIso f f' g g' h).hom.app U).op :=
  congrArg (fun a => (a.app F).hom.app (op U))
    (directImageSquareIso_transform f f' g g' h)

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) [Etale g]

/-- The genuine restriction comparison, transported by the original inverse-image isomorphisms. -/
def etaleBaseChangeIso :
    directImage f ⋙ inverseImage g ≅
      inverseImage (pullback.snd g f) ⋙ directImage (pullback.fst g f) :=
  Functor.isoWhiskerLeft (directImage f) (inverseImageEtaleIso g) ≪≫
    etaleDirectImageRestrictionIso f g ≪≫
      Functor.isoWhiskerRight (inverseImageEtaleIso (pullback.snd g f)).symm
        (directImage (pullback.fst g f))

private theorem etaleRestriction_directImage_unit (F : AbelianSheaf.{u, u + 1} X) :
    (((siteEtalePostcomposeAdj g).sheafPushforwardContinuous
      (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology T)
      (Scheme.smallEtaleTopology S)).unit.app ((directImage f).obj F)) ≫
        (directImage g).map ((etaleDirectImageRestrictionIso f g).hom.app F) =
      (directImage f).map
        (((siteEtalePostcomposeAdj (pullback.snd g f)).sheafPushforwardContinuous
          (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology (pullback g f))
          (Scheme.smallEtaleTopology X)).unit.app F) ≫
        (directImageSquareIso f (pullback.fst g f) g (pullback.snd g f)
          pullback.condition).hom.app ((etaleRestriction (pullback.snd g f)).obj F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change F.obj.map ((siteBaseChange f).map ((siteEtalePostcomposeAdj g).counit.app U.unop)).op ≫
      F.obj.map ((siteEtaleDirectImageRestrictionIso f g).hom.app
        ((siteBaseChange g).obj U.unop)).op =
    F.obj.map ((siteEtalePostcomposeAdj (pullback.snd g f)).counit.app
      ((siteBaseChange f).obj U.unop)).op ≫
        ((directImageSquareIso f (pullback.fst g f) g (pullback.snd g f)
          pullback.condition).hom.app ((etaleRestriction (pullback.snd g f)).obj F)).hom.app U
  rw [directImageSquareIso_app_hom]
  change _ = F.obj.map
    ((siteEtalePostcomposeAdj (pullback.snd g f)).counit.app
      ((siteBaseChange f).obj U.unop)).op ≫
    F.obj.map ((siteEtalePostcompose (pullback.snd g f)).map
      ((siteBaseChangeSquareIso f (pullback.fst g f) g (pullback.snd g f)
        pullback.condition).hom.app U.unop)).op
  exact ((F.obj.map_comp _ _).symm).trans
    ((congrArg (fun a => F.obj.map a.op)
      (siteEtaleDirectImageRestriction_counit f g U.unop).symm).trans
      (F.obj.map_comp _ _))

/-- The ordinary étale chart isomorphism is exactly the original underived exchange. -/
theorem etaleBaseChangeIso_hom :
    (etaleBaseChangeIso f g).hom =
      baseChangeMap f (pullback.fst g f) g (pullback.snd g f) pullback.condition := by
  exact exchange_of_restriction (directImage f) (directImage (pullback.fst g f))
    (inverseImageAdjunction (pullback.snd g f)) (inverseImageAdjunction g)
    ((siteEtalePostcomposeAdj (pullback.snd g f)).sheafPushforwardContinuous
      (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology (pullback g f))
      (Scheme.smallEtaleTopology X))
    ((siteEtalePostcomposeAdj g).sheafPushforwardContinuous
      (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology T)
      (Scheme.smallEtaleTopology S))
    (inverseImageEtaleIso (pullback.snd g f)) (inverseImageEtaleIso g)
    (etaleDirectImageRestrictionIso f g)
    (directImageSquareIso f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition).hom
    (baseChangeMap f (pullback.fst g f) g (pullback.snd g f) pullback.condition)
    (inverseImageEtaleIso_unit (pullback.snd g f)) (inverseImageEtaleIso_unit g)
    (etaleRestriction_directImage_unit f g)
    (baseChangeMap_horizontal_unit f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition)

/-- Ordinary base change along an étale chart is an isomorphism for all abelian coefficients. -/
instance baseChangeMap_etale_isIso :
    IsIso (baseChangeMap f (pullback.fst g f) g (pullback.snd g f) pullback.condition) := by
  rw [← etaleBaseChangeIso_hom f g]
  infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology
