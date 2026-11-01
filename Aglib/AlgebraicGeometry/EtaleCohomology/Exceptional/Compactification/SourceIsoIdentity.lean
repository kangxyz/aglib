/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.SourceIsoCompatibility
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.Identity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.LowerShriekComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.InverseImageTorsionCoherence

/-! # Original source-isomorphism normalization at the geometric identity -/
@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
private theorem rawSource_identity_algebra
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (F : A ⥤ B) (R : B ⥤ D) {x y : A}
    (s : F.obj x ⟶ F.obj y) (d : y ⟶ x)
    (h : s ≫ F.map d ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _) :
    (R.map s ≫ 𝟙 _ ≫ 𝟙 _ ≫ R.map (F.map (𝟙 y)) ≫ 𝟙 _) ≫
      R.map (F.map (d ≫ 𝟙 x)) ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _ := by
  simp only [Category.comp_id] at h
  simp only [Category.id_comp, Category.comp_id, Category.assoc, ← Functor.map_comp, h]
  exact R.map_id _

universe u dX dM dS
variable {X M : Scheme.{u}} (j : X ⟶ M) [IsOpenImmersion j]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{dX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{dM} (ModuleSheaf M Λ)]

private theorem lowerSource_identity_aux (i : X ⟶ M) [IsOpenImmersion i]
    (hi : i = j) (sq : IsPullback (𝟙 X) i j (𝟙 M)) :
    (Functor.rightUnitor (moduleDerivedLowerShriek j Λ)).symm ≪≫
      Functor.isoWhiskerLeft (moduleDerivedLowerShriek j Λ)
        (moduleDerivedInverseImageIdIso Λ M).symm ≪≫
      moduleDerivedLowerShriekCartesianBaseChangeIso (𝟙 X) i j (𝟙 M) sq Λ ≪≫
      Functor.isoWhiskerRight (moduleDerivedInverseImageIdIso Λ X)
        (moduleDerivedLowerShriek i Λ) ≪≫ Functor.leftUnitor _ ≪≫
      eqToIso (moduleDerivedLowerShriek_congr Λ hi) = Iso.refl _ := by
  subst i
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have h := moduleDerivedOpenComparison_identity Λ j sq K
  change (moduleDerivedInverseImageIdIso Λ M).hom.app _ = _ ≫ _ at h
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp, Category.comp_id]
  erw [Category.comp_id, ← h, Iso.inv_hom_id_app]
  rfl

/-- The original source comparison at reflexivity retains the actual equality `id ≫ j = j`. -/
theorem moduleDerivedLowerShriekSourceIso_refl :
    moduleDerivedLowerShriekSourceIso (Iso.refl X) j Λ ≪≫
      Functor.isoWhiskerRight (moduleDerivedInverseImageIdIso Λ X)
        (moduleDerivedLowerShriek ((𝟙 X) ≫ j) Λ) ≪≫
      Functor.leftUnitor _ ≪≫
      eqToIso (moduleDerivedLowerShriek_congr Λ (Category.id_comp j)) = Iso.refl _ := by
  simpa only [moduleDerivedLowerShriekSourceIso, Iso.refl_hom, Iso.trans_assoc] using
    lowerSource_identity_aux j Λ (𝟙 X ≫ j) (Category.id_comp j)
      (isPullback_sourceIsoOpen (Iso.refl X) j)

section Raw
variable {S : Scheme.{u}} {f : X ⟶ S} (C : Hom.Compactification f)
  [HasDerivedCategory.{dS} (ModuleSheaf S Λ)]
  [hC : HasDerivedCategory.{dM} (ModuleSheaf C.Xbar Λ)]
/-- The local derived-category model on `ModuleSheaf (C.ofSourceIso f (Iso.refl X)
(Category.id_comp f)).Xbar Λ`. -/
local instance sourceIsoIdentityRawAmbientModel : HasDerivedCategory.{dM}
    (ModuleSheaf (C.ofSourceIso f (Iso.refl X) (Category.id_comp f)).Xbar Λ) := hC

/-- The actual source-transported raw value is equal after the original geometric identity law. -/
theorem moduleRawCompactificationFunctor_source_refl :
    @moduleRawCompactificationFunctor X S f
      (C.ofSourceIso f (Iso.refl X) (Category.id_comp f)) Λ _
      inferInstance inferInstance inferInstance = moduleRawCompactificationFunctor C Λ := by
  (simp only [moduleRawCompactificationFunctor, Hom.Compactification.ofSourceIso,
    Iso.refl_hom, Category.id_comp, sourceIsoIdentityRawAmbientModel]; rfl)

/-- Reflexive raw source transport normalizes by the original torsion identity,
not by an identification of source-transported compactifications. -/
theorem moduleRawCompactificationSourceIso_refl :
    moduleRawCompactificationSourceIso (Iso.refl X) Λ f (Category.id_comp f) C ≪≫
      Functor.isoWhiskerRight (moduleDerivedInverseImageTorsionIdIso Λ X)
        (moduleRawCompactificationFunctor
          (C.ofSourceIso f (Iso.refl X) (Category.id_comp f)) Λ) ≪≫
      Functor.leftUnitor _ ≪≫
      eqToIso (moduleRawCompactificationFunctor_source_refl Λ C) = Iso.refl _ := by
  have h := moduleDerivedLowerShriekSourceIso_refl C.j Λ
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hk := congrArg (fun z => z.hom.app K.obj) h
  change (moduleDerivedLowerShriekSourceIso (Iso.refl X) C.j Λ).hom.app K.obj ≫
    (moduleDerivedLowerShriek C.j Λ).map ((moduleDerivedInverseImageIdIso Λ X).hom.app K.obj) ≫
    𝟙 _ ≫ 𝟙 _ = 𝟙 _ at hk
  dsimp only [moduleRawCompactificationSourceIso, sourceIsoAmbientModel,
    moduleRawCompactificationFunctor,
    Hom.Compactification.ofSourceIso, Iso.refl_hom, Category.id_comp,
    moduleDerivedInverseImageTorsionIdIso, moduleDerivedInverseImageTorsionForgetIso,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app, Functor.comp_map,
    Functor.map_comp, Functor.map_id, Category.comp_id, Category.id_comp,
    eqToIso_refl, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    ObjectProperty.ι_map, ObjectProperty.liftFunctorIso_hom_app]
  exact rawSource_identity_algebra (moduleDerivedLowerShriek C.j Λ)
    (moduleDerivedDirectImage Λ C.p)
    ((moduleDerivedLowerShriekSourceIso (Iso.refl X) C.j Λ).hom.app K.obj)
    ((moduleDerivedInverseImageIdIso Λ X).hom.app K.obj) hk
end Raw

end AlgebraicGeometry.Scheme.EtaleCohomology
