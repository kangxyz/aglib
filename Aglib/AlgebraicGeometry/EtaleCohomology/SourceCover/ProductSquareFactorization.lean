/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.ProductSquare

/-! # Original source-product square through composite chart squares

The factorization uses the original site compositors and actual chart
restriction square. Equality is checked on the original pullback projections.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge
open MorphismProperty.Over

variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (H : IsPullback g' f' f g)

/-- The complete original site path through the composite source chart square
is the original source-product square, component by component. -/
theorem sourceEtaleProductSquare_factorization (U : X.Etale) (T : S.Etale) :
    (siteEtalePostcompose ((siteBaseChange g').obj U).hom).map
        ((siteBaseChangeComp f' ((siteBaseChange g').obj U).hom).inv.app
          ((siteBaseChange g).obj T)) ≫
      (siteEtalePostcompose ((siteBaseChange g').obj U).hom).map
        ((siteBaseChangeSquareIso (U.hom ≫ f)
          (((siteBaseChange g').obj U).hom ≫ f') g (pullback.fst U.hom g')
          ((IsPullback.of_hasPullback U.hom g').paste_vert H).w.symm).hom.app T) ≫
      (siteEtaleDirectImageRestrictionIso g' U.hom).hom.app
        ((siteBaseChange (U.hom ≫ f)).obj T) ≫
      (siteBaseChange g').map ((siteEtalePostcompose U.hom).map
        ((siteBaseChangeComp f U.hom).hom.app T)) =
    (sourceEtaleProductSquare f f' g g' H.w.symm U).hom.app T := by
  have hs := siteBaseChangeSquareIso_fst_fst f f' g g' H.w.symm T
  have ht := siteBaseChangeSquareIso_fst_fst (U.hom ≫ f)
    (((siteBaseChange g').obj U).hom ≫ f') g (pullback.fst U.hom g')
    ((IsPullback.of_hasPullback U.hom g').paste_vert H).w.symm T
  have ws := MorphismProperty.Over.w
    ((siteBaseChangeSquareIso f f' g g' H.w.symm).hom.app T)
  have wt := MorphismProperty.Over.w
    ((siteBaseChangeSquareIso (U.hom ≫ f)
      (((siteBaseChange g').obj U).hom ≫ f') g (pullback.fst U.hom g')
      ((IsPullback.of_hasPullback U.hom g').paste_vert H).w.symm).hom.app T)
  simp only [Functor.comp_obj, siteBaseChange,
    MorphismProperty.Over.pullback_obj_hom] at ht ws wt
  let U' := (siteBaseChange g').obj U
  let Tf := (siteBaseChange f).obj T
  let e := productBaseChangeIso etaleMorphismProperty etaleMorphismProperty
    (siteBaseChange g') U Tf
  apply (cancel_mono e.hom).1
  change _ = ((etaleProductTest U').map
    ((siteBaseChangeSquareIso f f' g g' H.w.symm).hom.app T) ≫ e.inv) ≫ e.hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_mono (productIso etaleMorphismProperty U'
    ((siteBaseChange g').obj Tf)).hom).1
  apply prod.hom_ext
  · simp only [e, U', Tf, Category.assoc, productIso_hom_fst,
      productBaseChangeIso_fst, productTest_map_fst]
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [productFst, siteEtalePostcompose, siteBaseChange,
          siteEtaleDirectImageRestrictionIso_hom_left, Category.assoc,
          siteBaseChangeComp, hs, ht]
      · simp [productFst, siteEtalePostcompose, siteBaseChange,
          siteEtaleDirectImageRestrictionIso_hom_left, Category.assoc,
          siteBaseChangeComp, reassoc_of% ws, reassoc_of% wt,
          pullback.condition, pullback.condition_assoc]
    · simp [productFst, siteEtalePostcompose, siteBaseChange,
        siteEtaleDirectImageRestrictionIso_hom_left, Category.assoc,
        siteBaseChangeComp, ws, reassoc_of% wt, pullback.condition]
  · simp only [e, U', Tf, Category.assoc, productIso_hom_snd,
      productBaseChangeIso_snd]
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext <;>
      simp [productSnd, siteEtalePostcompose, siteBaseChange,
        siteEtaleDirectImageRestrictionIso_hom_left, Category.assoc,
        siteBaseChangeComp, reassoc_of% wt, pullback.condition]

end AlgebraicGeometry.Scheme.EtaleCohomology
