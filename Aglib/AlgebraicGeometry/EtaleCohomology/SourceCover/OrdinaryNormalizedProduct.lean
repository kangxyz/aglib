/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.OrdinaryMateHeads
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.ProductSquareFactorization

/-! # Identification with the original product-test mate

The equality uses the complete original site factorization. No equality of
chosen products or implicit higher base-change theorem is assumed.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge

local instance {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) :
    (siteBaseChange f ⋙ siteBaseChange g).IsContinuous
      (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology T) :=
  Functor.isContinuous_comp _ _ _ (Scheme.smallEtaleTopology S) _

private theorem comp_hom_transform {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) :
    (directImageCompIso f g).hom =
      Functor.sheafPushforwardContinuousNatTrans (siteBaseChangeComp f g).hom
        AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology X)
        (Scheme.smallEtaleTopology T) := by
  exact Category.id_comp _

private theorem comp_inv_transform {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) :
    (directImageCompIso f g).inv =
      Functor.sheafPushforwardContinuousNatTrans (siteBaseChangeComp f g).inv
        AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology X)
        (Scheme.smallEtaleTopology T) := by
  exact Category.comp_id _

variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (H : IsPullback g' f' f g)

private theorem source_square_head (U : X.Etale) :
    siteBaseChangeSquareIso (U.hom ≫ f) (pullback.snd U.hom g' ≫ f') g
      (pullback.fst U.hom g') (sourceEtaleCompositeSquare f f' g g' H U).w.symm =
    siteBaseChangeSquareIso (U.hom ≫ f) (((siteBaseChange g').obj U).hom ≫ f') g
      (pullback.fst U.hom g') (sourceEtaleCompositeSquare f f' g g' H U).w.symm := rfl

/-- The normalized direct-image word is the original product-test map. -/
theorem sourceEtaleNormalizedProduct_app (U : X.Etale)
    (F : AbelianSheaf.{u, u + 1} X') :
    (SourceChartMates.rightIso (etaleDirectImageRestrictionIso g' U.hom)
      (directImageSquareIso (U.hom ≫ f) (pullback.snd U.hom g' ≫ f') g
        (pullback.fst U.hom g') (sourceEtaleCompositeSquare f f' g g' H U).w.symm)
      (sourceEtaleImageRestrictionIso f U)
      (sourceEtaleImageRestrictionIso f' ((siteBaseChange g').obj U))).hom.app F =
        (sourceEtaleDirectImageSquare f f' g g' H.w.symm U).hom.app F := by
  dsimp only [SourceChartMates.rightIso, sourceEtaleImageRestrictionIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.id_comp, Category.comp_id,
    Category.assoc]
  rw [comp_hom_transform, comp_inv_transform, directImageSquareIso_transform]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  change F.obj.map _ ≫ F.obj.map _ ≫ F.obj.map _ ≫ F.obj.map _ = F.obj.map _
  rw [← F.obj.map_comp, ← F.obj.map_comp, ← F.obj.map_comp]
  simp only [Functor.op_map, Functor.op_obj, NatTrans.op_app, Functor.comp_obj,
    Iso.symm_inv, Quiver.Hom.unop_op]
  erw [source_square_head f f' g g' H U]
  simpa only [op_comp, Category.assoc] using congrArg (fun k => F.obj.map k.op)
    (sourceEtaleProductSquare_factorization f f' g g' H U T.unop)


end AlgebraicGeometry.Scheme.EtaleCohomology
