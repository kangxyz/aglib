/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.RelativeAffine

/-! # Actual affine structural schemes and original relative pullbacks

Native gluing squares and the original affine-source comparison identify each
structural affine scheme with the actual relative pullback over the original
Spec chart. Both original projections are retained in the actual Over iso.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

universe u

open AffineZariskiSite

/-- The native gluing square over the actual Spec affine chart, retaining
the original structural ring map. -/
theorem relativeGluing_affineChart_isPullback {X : Scheme.{u}}
    {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
    {a : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F}
    (ha : a.Coequifibered) (U : X.AffineZariskiSite) :
    IsPullback ((relativeGluingData ha).cover.f U) (Spec.map (a.app (op U)))
      (relativeGluingData ha).toBase U.2.fromSpec := by
  let d := relativeGluingData ha
  have hs := d.isPullback_natTrans_ι_toBase U
  refine (hs.of_iso (Iso.refl _) U.2.isoSpec (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_).flip
  · change (Spec.map (a.app (op U)) ≫ U.2.isoSpec.inv) ≫ U.2.isoSpec.hom =
      𝟙 _ ≫ Spec.map (a.app (op U))
    exact (Category.assoc (Spec.map (a.app (op U))) U.2.isoSpec.inv U.2.isoSpec.hom).trans
      ((congrArg (fun k => Spec.map (a.app (op U)) ≫ k) U.2.isoSpec.inv_hom_id).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm))
  · change d.cover.f U ≫ 𝟙 d.glued = 𝟙 _ ≫ d.cover.f U
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · change U.1.ι ≫ 𝟙 X = U.2.isoSpec.hom ≫ (U.2.isoSpec.inv ≫ U.1.ι)
    exact (Category.comp_id U.1.ι).trans
      ((Category.assoc U.2.isoSpec.hom U.2.isoSpec.inv U.1.ι).symm.trans
        ((congrArg (fun k => k ≫ U.1.ι) U.2.isoSpec.hom_inv_id).trans
          (Category.id_comp _))).symm
  · change d.toBase ≫ 𝟙 X = 𝟙 d.glued ≫ d.toBase
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The original affine source is the pullback of its original structural
ring map over the actual Spec chart. -/
theorem relativeAffineChart_isPullback {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsAffineHom f] (U : X.AffineZariskiSite) :
    IsPullback (U.2.preimage f).fromSpec (Spec.map (f.app U.1)) f U.2.fromSpec := by
  let d := relativeAffineData f
  let e := relativeSourceIso f
  have hs := relativeGluing_affineChart_isPullback (relativeSectionMap_coequifibered f) U
  apply hs.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
  · exact (relativeCover_toSource f U).trans (Category.id_comp _).symm
  · change Spec.map (f.app U.1) ≫ 𝟙 _ = 𝟙 _ ≫ Spec.map (f.app U.1)
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id d.toBase).trans (relativeSourceIso_hom_over f).symm
  · change U.2.fromSpec ≫ 𝟙 X = 𝟙 _ ≫ U.2.fromSpec
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The original affine structural scheme as an actual relative pullback
object, through its original cartesian chart. -/
def relativeAffineChartObjectIso {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsAffineHom f] (U : X.AffineZariskiSite) :
    Over.mk (Spec.map (f.app U.1)) ≅
      (Over.pullback U.2.fromSpec).obj (Over.mk f) :=
  Over.isoMk (relativeAffineChart_isPullback f U).isoPullback
    (relativeAffineChart_isPullback f U).isoPullback_hom_snd

/-- The generated chart as an actual relative pullback object. -/
def relativeGluingChartObjectIso {X : Scheme.{u}}
    {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
    {a : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F}
    (ha : a.Coequifibered) (U : X.AffineZariskiSite) :
    Over.mk (Spec.map (a.app (op U))) ≅
      (Over.pullback U.2.fromSpec).obj (Over.mk (relativeGluingData ha).toBase) :=
  Over.isoMk (relativeGluing_affineChart_isPullback ha U).isoPullback
    (relativeGluing_affineChart_isPullback ha U).isoPullback_hom_snd

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
