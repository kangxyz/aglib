/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Sites.RepresentedTransfer.ProductBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.Images
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleDirectImageSiteSquare

/-! # Original source-chart product square

This is a site-level comparison, with its literal face identity. Identification
of its sheaf mate with composite-chart ordinary exchange is a separate step.
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
  (h : f' ≫ g = g' ≫ f)

local instance productSourceContinuous (U : X.Etale) :
    (siteBaseChange f ⋙ etaleProductTest U).IsContinuous
      (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X) :=
  Functor.isContinuous_comp _ _ _ (Scheme.smallEtaleTopology X) _

local instance productSourceTargetContinuous (U : X.Etale) :
    ((siteBaseChange f ⋙ etaleProductTest U) ⋙ siteBaseChange g').IsContinuous
      (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X') :=
  Functor.isContinuous_comp _ _ _ (Scheme.smallEtaleTopology X) _

local instance productTargetSourceContinuous (U : X.Etale) :
    (siteBaseChange g ⋙ (siteBaseChange f' ⋙
      etaleProductTest ((siteBaseChange g').obj U))).IsContinuous
      (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X') :=
  Functor.isContinuous_comp _ _ _ (Scheme.smallEtaleTopology S') _

/-- The complete original product-test square, before sheaf pushforward. -/
def sourceEtaleProductSquare (U : X.Etale) :
    siteBaseChange g ⋙ (siteBaseChange f' ⋙ etaleProductTest ((siteBaseChange g').obj U)) ≅
      (siteBaseChange f ⋙ etaleProductTest U) ⋙ siteBaseChange g' :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (siteBaseChangeSquareIso f f' g g' h)
      (etaleProductTest ((siteBaseChange g').obj U)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (siteBaseChange f)
      (MorphismProperty.Over.productBaseChangeNatIso etaleMorphismProperty etaleMorphismProperty
        (siteBaseChange g') U).symm ≪≫
    (Functor.associator _ _ _).symm

/-- Fixed source-chart faces commute at every original target test. -/
theorem sourceEtaleProductSquare_face {U V : X.Etale} (a : U ⟶ V) (T : S.Etale) :
    (sourceEtaleProductSquare f f' g g' h U).hom.app T ≫
      (siteBaseChange g').map ((etaleProductMap a).app ((siteBaseChange f).obj T)) =
    (etaleProductMap ((siteBaseChange g').map a)).app
        ((siteBaseChange f').obj ((siteBaseChange g).obj T)) ≫
      (sourceEtaleProductSquare f f' g g' h V).hom.app T := by
  change (etaleProductTest ((siteBaseChange g').obj U)).map
      ((siteBaseChangeSquareIso f f' g g' h).hom.app T) ≫
      (MorphismProperty.Over.productBaseChangeIso etaleMorphismProperty
        etaleMorphismProperty (siteBaseChange g') U
        ((siteBaseChange f).obj T)).inv ≫ _ = _
  rw [MorphismProperty.Over.productBaseChangeIso_inv_face]
  have hn := (MorphismProperty.Over.productMap etaleMorphismProperty
    ((siteBaseChange g').map a)).naturality
      ((siteBaseChangeSquareIso f f' g g' h).hom.app T)
  simpa only [etaleProductTest, etaleProductMap, Functor.comp_obj,
    MorphismProperty.Over.productBaseChangeNatIso, NatIso.ofComponents_inv_app,
    sourceEtaleProductSquare, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, Category.assoc] using congrArg
    (fun z => z ≫ (MorphismProperty.Over.productBaseChangeIso
      etaleMorphismProperty etaleMorphismProperty (siteBaseChange g') V
        ((siteBaseChange f).obj T)).inv) hn

/-- Original direct images of source products commute through the site square. -/
def sourceEtaleDirectImageSquare (U : X.Etale) :
    directImage g' ⋙ sourceEtaleImage f U ≅
      sourceEtaleImage f' ((siteBaseChange g').obj U) ⋙ directImage g :=
  (Functor.sheafPushforwardContinuousIso
    (sourceEtaleProductSquare f f' g g' h U) AddCommGrpCat.{u + 1}
    (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X')).symm

/-- The sheaf comparison preserves the unchanged original source faces. -/
theorem sourceEtaleDirectImageSquare_face {U V : X.Etale} (a : U ⟶ V) :
    Functor.whiskerLeft (directImage g')
        (Functor.whiskerRight (etaleProductSheafMap a) (directImage f)) ≫
      (sourceEtaleDirectImageSquare f f' g g' h U).hom =
    (sourceEtaleDirectImageSquare f f' g g' h V).hom ≫
      Functor.whiskerRight
        (Functor.whiskerRight (etaleProductSheafMap ((siteBaseChange g').map a))
          (directImage f')) (directImage g) := by
  apply NatTrans.ext
  funext F
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
  rw [← F.obj.map_comp, ← F.obj.map_comp]
  exact congrArg (fun k => F.obj.map k.op)
    (sourceEtaleProductSquare_face f f' g g' h a T.unop)

end AlgebraicGeometry.Scheme.EtaleCohomology
