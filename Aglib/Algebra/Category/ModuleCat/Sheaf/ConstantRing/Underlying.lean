/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Pullback
public import Aglib.CategoryTheory.Sites.Pullback.Coefficients
public import Aglib.CategoryTheory.Adjunction.UnderlyingEquivalence
public import Aglib.CategoryTheory.Adjunction.UnderlyingMate

/-! # Actual underlying abelian comparisons for arbitrary constant rings

The original coefficient equivalence, native images and preserved Kan/sheafification
comparison construct the underlying functor families. Their unit normalization uses
native module sheafification and the actual coefficient-equivalence counit.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.Sheaf.ConstantRing

universe u₁ v₁ u₂ v₂ r w

/-- Keep the actual endpoint fixed while adding a categorical identity to a value equation. -/
private theorem eq_comp_id_value {T : Type*} [Category* T] {A B : T}
    (f g : A ⟶ B) (h : f = g) : f = g ≫ 𝟙 B :=
  h.trans (Category.comp_id g).symm

/-- Keep the actual endpoint fixed while adding a categorical identity to the first value. -/
private theorem comp_id_eq_value {T : Type*} [Category* T] {A B : T}
    (f g : A ⟶ B) (h : f = g) : f ≫ 𝟙 B = g :=
  (Category.comp_id f).trans h

/-- Insert an identity before specializing the actual intermediate object. -/
private theorem insert_id_comp_value {T : Type*} [Category* T] {A B C : T}
    (f : A ⟶ B) (g : B ⟶ C) (z : A ⟶ C) (h : f ≫ g = z) :
    f ≫ 𝟙 B ≫ g = z := by
  simpa only [Category.id_comp] using h

/-- Remove an identity before specializing the actual intermediate object. -/
private theorem remove_id_comp_value {T : Type*} [Category* T] {A B C : T}
    (f : A ⟶ B) (g : B ⟶ C) (z : A ⟶ C) (h : f ≫ 𝟙 B ≫ g = z) :
    f ≫ g = z := by
  simpa only [Category.id_comp] using h

section SingleSite

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  (Λ : Type r) [Ring Λ]
  [HasWeakSheafify J RingCat.{r}] [J.WEqualsLocallyBijective RingCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- The inverse equivalence retains the same original abelian sheaf. -/
def moduleSheafInverseUnderlyingIso :
    (moduleSheafEquivalence J Λ).inverse ⋙
      sheafCompose J
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ≅
      SheafOfModules.toSheaf (constantRing J Λ) :=
  Functor.isoWhiskerLeft (moduleSheafEquivalence J Λ).inverse
    (moduleSheafUnderlyingIso J Λ).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleSheafEquivalence J Λ).counitIso
      (SheafOfModules.toSheaf (constantRing J Λ)) ≪≫
    Functor.leftUnitor _

/-- The inverse underlying comparison retains the original four isomorphism factors. -/
theorem moduleSheafInverseUnderlyingIso_eq_original :
    moduleSheafInverseUnderlyingIso J Λ =
      Functor.isoWhiskerLeft (moduleSheafEquivalence J Λ).inverse
        (moduleSheafUnderlyingIso J Λ).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (moduleSheafEquivalence J Λ).counitIso
        (SheafOfModules.toSheaf (constantRing J Λ)) ≪≫ Functor.leftUnitor _ := rfl

/-- The counit of the original coefficient equivalence has its prescribed
abelian-sheafification comparison underneath. -/
@[reassoc]
theorem moduleSheafEquivalence_counit_underlying (M : ModuleSheaf.{u₁, v₁, r, w} J Λ) :
    (SheafOfModules.toSheaf (constantRing J Λ)).map
        ((moduleSheafEquivalence J Λ).counitIso.hom.app M) =
      (moduleSheafUnderlyingIso J Λ).hom.app
        ((moduleSheafEquivalence J Λ).inverse.obj M) := by
  let C₀ := ModuleCat.Sheaf.ConstantRing.constantSheafEquivalence.{u₁, v₁, r, w}
    J Λ
  let E := constantModuleSheafificationEquivalence J Λ
  let V := ModuleCat.Sheaf.ConstantRing.moduleUnderlyingSheaf.{u₁, v₁, r, w}
    J
    ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))
  let U := SheafOfModules.toSheaf (constantRing J Λ)
  let c := constantModuleSheafificationUnderlyingIso J Λ
  let d := ModuleCat.Sheaf.ConstantRing.constantSheafUnderlyingIso.{u₁, v₁, r, w}
    J Λ
  have hc : V.map (C₀.counitIso.hom.app (E.inverse.obj M)) =
      d.hom.app (C₀.inverse.obj (E.inverse.obj M)) := by
    apply ObjectProperty.hom_ext
    ext W x
    rfl
  have hE : U.map (E.counitIso.hom.app M) =
      c.hom.app (E.inverse.obj M) := by
    exact PresheafOfModules.toSheaf_map_sheafificationAdjunction_counit_app
      (constantRingUnit J Λ) M
  simp only [moduleSheafEquivalence, moduleSheafUnderlyingIso]
  change U.map (E.functor.map (C₀.counitIso.hom.app (E.inverse.obj M))) ≫
      U.map (E.counitIso.hom.app M) =
    c.hom.app (C₀.functor.obj (C₀.inverse.obj (E.inverse.obj M))) ≫
      d.hom.app (C₀.inverse.obj (E.inverse.obj M))
  erw [hE, c.hom.naturality, hc]
  rfl

/-- The inverse counit retains the inverse of the specified underlying comparison. -/
theorem moduleSheafEquivalence_counit_inv_underlying (M : ModuleSheaf.{u₁, v₁, r, w} J Λ) :
    (SheafOfModules.toSheaf (constantRing J Λ)).map
        ((moduleSheafEquivalence J Λ).counitIso.inv.app M) =
      (moduleSheafUnderlyingIso J Λ).inv.app
        ((moduleSheafEquivalence J Λ).inverse.obj M) := by
  have h : (SheafOfModules.toSheaf (constantRing J Λ)).mapIso
      ((moduleSheafEquivalence J Λ).counitIso.app M) =
      (moduleSheafUnderlyingIso J Λ).app
        ((moduleSheafEquivalence J Λ).inverse.obj M) :=
    Iso.ext (moduleSheafEquivalence_counit_underlying J Λ M)
  exact congrArg Iso.inv h

/-- The already specified inverse-equivalence comparison is the identity on the
original abelian sheaf. -/
theorem moduleSheafInverseUnderlyingIso_hom_app (M : ModuleSheaf.{u₁, v₁, r, w} J Λ) :
    (moduleSheafInverseUnderlyingIso J Λ).hom.app M =
      𝟙 ((SheafOfModules.toSheaf (constantRing J Λ)).obj M) := by
  simp only [moduleSheafInverseUnderlyingIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp]
  erw [moduleSheafEquivalence_counit_underlying, Iso.inv_hom_id_app_assoc]

/-- The fixed inverse-equivalence comparison is the identity natural isomorphism. -/
theorem moduleSheafInverseUnderlyingIso_eq_refl :
    moduleSheafInverseUnderlyingIso J Λ =
      Iso.refl (SheafOfModules.toSheaf (constantRing J Λ)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  exact moduleSheafInverseUnderlyingIso_hom_app J Λ M

/-- The equivalence unit becomes the inverse of the existing underlying comparison. -/
theorem moduleSheafEquivalence_unit_underlying (M : ModuleValuedSheaf.{u₁, v₁, r, w} J Λ) :
    (sheafCompose J
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
          ((moduleSheafEquivalence J Λ).unitIso.hom.app M) =
      (moduleSheafUnderlyingIso J Λ).inv.app M := by
  exact Equivalence.unit_map_eq_inv (moduleSheafEquivalence J Λ)
    (sheafCompose J
      (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}))
    (moduleSheafUnderlyingIso J Λ)
    (moduleSheafEquivalence_counit_underlying J Λ) M

/-- Whole counit normalization retains the original underlying functors and comparisons. -/
theorem moduleSheafEquivalence_counit_underlying_whole :
    Functor.whiskerRight (moduleSheafEquivalence J Λ).counitIso.hom
        (SheafOfModules.toSheaf.{w} (constantRing J Λ)) ≫
      (Functor.leftUnitor (SheafOfModules.toSheaf.{w} (constantRing J Λ))).hom =
      (Functor.associator (moduleSheafEquivalence J Λ).inverse
        (moduleSheafEquivalence J Λ).functor
        (SheafOfModules.toSheaf.{w} (constantRing J Λ))).hom ≫
      Functor.whiskerLeft (moduleSheafEquivalence J Λ).inverse
        (moduleSheafUnderlyingIso J Λ).hom ≫
      (moduleSheafInverseUnderlyingIso J Λ).hom := by
  rw [moduleSheafInverseUnderlyingIso_eq_refl]
  apply NatTrans.ext
  funext M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.leftUnitor_hom_app, Iso.refl_hom,
    NatTrans.id_app, Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id]
  exact eq_comp_id_value
    (A := (SheafOfModules.toSheaf.{w} (constantRing J Λ)).obj
      ((moduleSheafEquivalence J Λ).functor.obj ((moduleSheafEquivalence J Λ).inverse.obj M)))
    (B := (SheafOfModules.toSheaf.{w} (constantRing J Λ)).obj M) _ _
    (moduleSheafEquivalence_counit_underlying J Λ M)

/-- Whole unit normalization retains the original underlying functors and comparisons. -/
theorem moduleSheafEquivalence_unit_underlying_whole :
    (Functor.leftUnitor
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}))).inv ≫
      Functor.whiskerRight (moduleSheafEquivalence J Λ).unitIso.hom
        (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})) ≫
      (Functor.associator (moduleSheafEquivalence J Λ).functor
        (moduleSheafEquivalence J Λ).inverse
        (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}))).hom ≫
      Functor.whiskerLeft (moduleSheafEquivalence J Λ).functor
        (moduleSheafInverseUnderlyingIso J Λ).hom =
      (moduleSheafUnderlyingIso J Λ).inv := by
  rw [moduleSheafInverseUnderlyingIso_eq_refl]
  apply NatTrans.ext
  funext M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.leftUnitor_inv_app, Iso.refl_hom,
    NatTrans.id_app, Functor.comp_obj, Functor.id_obj, Category.id_comp]
  exact comp_id_eq_value
    (A := (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj M)
    (B := (SheafOfModules.toSheaf.{w} (constantRing J Λ)).obj
      ((moduleSheafEquivalence J Λ).functor.obj M)) _ _
    (moduleSheafEquivalence_unit_underlying J Λ M)

end SingleSite

section Images

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (Λ : Type r) [Ring Λ] [F.IsContinuous J K]

section Valued

variable [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [∀ P : Cᵒᵖ ⥤ ModuleCat.{w} Λ, F.op.HasLeftKanExtension P]
  [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, F.op.HasLeftKanExtension P]
  [HasWeakSheafify K (ModuleCat.{w} Λ)] [HasWeakSheafify K AddCommGrpCat.{w}]
  [(forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).PreservesLeftKanExtensions F.op]
  [K.PreservesSheafification (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- The original module-valued inverse image commutes with additive forgetting. -/
def moduleValuedInverseImageUnderlyingIso :
    moduleValuedInverseImage F J K Λ ⋙
      sheafCompose K
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ≅
    sheafCompose J
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ⋙
      F.sheafPullback AddCommGrpCat.{w} J K :=
  (Functor.sheafPullbackCoefficientIso F J K
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).symm

/-- The original module-valued unit becomes the original abelian unit. -/
theorem moduleValuedInverseImageUnderlyingIso_unit (M : ModuleValuedSheaf.{u₁, v₁, r, w} J Λ) :
    (sheafCompose J
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
          ((moduleValuedInverseImageAdjunction F J K Λ).unit.app M) ≫
      (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map
        ((moduleValuedInverseImageUnderlyingIso F J K Λ).hom.app M) =
    (F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app
      ((sheafCompose J
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj M) := by
  let U := forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}
  have h := Functor.sheafPullbackCoefficientIso_unit F
    J K U M
  change (F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app ((sheafCompose _ U).obj M) ≫
      (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map
        ((moduleValuedInverseImageUnderlyingIso F J K Λ).inv.app M) =
    (sheafCompose _ U).map ((moduleValuedInverseImageAdjunction F J K Λ).unit.app M) at h
  rw [← h]
  erw [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]

end Valued

variable [HasWeakSheafify J RingCat.{r}] [HasWeakSheafify K RingCat.{r}]

/-- The direct comparison component is identity at its literal abelian target object. -/
private theorem moduleDirectImageUnderlyingIso_hom_app_value
    (M : ModuleSheaf.{u₂, v₂, r, w} K Λ) :
    (moduleDirectImageUnderlyingIso F J K Λ).hom.app M =
      𝟙 ((F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj
        ((SheafOfModules.toSheaf.{w} (constantRing K Λ)).obj M)) := rfl

variable [J.WEqualsLocallyBijective RingCat.{r}] [K.WEqualsLocallyBijective RingCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- The inverse direct-image transport has exactly the existing coefficient
comparison underneath; restriction of scalars retains every additive map. -/
theorem moduleDirectImageTransportIso_inv_underlying (M : ModuleSheaf.{u₂, v₂, r, w} K Λ) :
    (SheafOfModules.toSheaf (constantRing J Λ)).map
        ((moduleDirectImageTransportIso F J K Λ).inv.app M) =
      (moduleSheafUnderlyingIso J Λ).hom.app
        ((moduleValuedDirectImage F J K Λ).obj
          ((moduleSheafEquivalence K Λ).inverse.obj M)) := by
  have hq : (sheafCompose J
      (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
        ((moduleDirectImageComparison F J K Λ).inv.app M) =
      𝟙 ((SheafOfModules.toSheaf (constantRing J Λ)).obj
        ((moduleDirectImage F J K Λ).obj M)) := by
    apply ObjectProperty.hom_ext
    ext W x
    rfl
  have ht := Equivalence.transportRightIso_inv_app (moduleSheafEquivalence J Λ)
    (moduleDirectImage F J K Λ) (moduleSheafEquivalence K Λ).inverse
    (moduleValuedDirectImage F J K Λ) (moduleDirectImageComparison F J K Λ) M
  have hn := Equivalence.map_functor_comp_counit (moduleSheafEquivalence J Λ)
    (sheafCompose J
      (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}))
    (moduleSheafUnderlyingIso J Λ)
    (moduleSheafEquivalence_counit_underlying J Λ)
    ((moduleDirectImageComparison F J K Λ).inv.app M)
  exact (congrArg (SheafOfModules.toSheaf (constantRing J Λ)).map ht).trans
    (hn.trans ((congrArg (fun k =>
      (moduleSheafUnderlyingIso J Λ).hom.app
        ((moduleValuedDirectImage F J K Λ).obj
          ((moduleSheafEquivalence K Λ).inverse.obj M)) ≫ k) hq).trans
      (Category.comp_id _)))

variable [∀ P : Cᵒᵖ ⥤ ModuleCat.{w} Λ, F.op.HasLeftKanExtension P]
  [HasWeakSheafify K (ModuleCat.{w} Λ)]

/-- The unit transported through the existing equivalences becomes the original
module-valued unit, after its specified underlying comparison. -/
@[reassoc]
theorem moduleTransportAdjunction_unit_underlying (M : ModuleSheaf.{u₁, v₁, r, w} J Λ) :
    (SheafOfModules.toSheaf (constantRing J Λ)).map
        ((moduleTransportAdjunction F J K Λ).unit.app M) ≫
      (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map
        ((moduleSheafUnderlyingIso K Λ).hom.app
        ((moduleValuedInverseImage F J K Λ).obj
          ((moduleSheafEquivalence J Λ).inverse.obj M))) =
      (sheafCompose J
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
          ((moduleValuedInverseImageAdjunction F J K Λ).unit.app
            ((moduleSheafEquivalence J Λ).inverse.obj M)) := by
  let EX := moduleSheafEquivalence J Λ
  let ES := moduleSheafEquivalence K Λ
  let U := SheafOfModules.toSheaf (constantRing J Λ)
  let V := sheafCompose J
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})
  let P := (moduleValuedInverseImage F J K Λ).obj (EX.inverse.obj M)
  let a := (moduleValuedInverseImageAdjunction F J K Λ).unit.app (EX.inverse.obj M)
  let b := (moduleValuedDirectImage F J K Λ).map (ES.unitIso.hom.app P)
  let k := (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map
    ((moduleSheafUnderlyingIso K Λ).hom.app P)
  have hk : V.map b ≫ k = 𝟙 _ := by
    have h := congrArg (fun z => (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map z ≫ k)
      (moduleSheafEquivalence_unit_underlying K Λ P)
    exact h.trans ((F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).mapIso
      ((moduleSheafUnderlyingIso K Λ).app P)).inv_hom_id
  have hn := NatIso.inv_map_map_hom_comp (moduleSheafUnderlyingIso J Λ) a b k hk
  have ht := Adjunction.equivalence_transport_unit EX ES
    (moduleValuedInverseImageAdjunction F J K Λ) (moduleDirectImageTransportIso F J K Λ) M
  have hm := congrArg (fun z => U.map z ≫ k) ht
  simp only [Functor.map_comp] at hm
  have hc := congrArg₂ (fun p q => p ≫ U.map (EX.functor.map a) ≫
      U.map (EX.functor.map b) ≫ q ≫ k)
    (moduleSheafEquivalence_counit_inv_underlying J Λ M)
    (moduleDirectImageTransportIso_inv_underlying F J K Λ (ES.functor.obj P))
  exact hm.trans (hc.trans hn)

variable [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, F.op.HasLeftKanExtension P]
  [(forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).PreservesLeftKanExtensions F.op]
  [K.PreservesSheafification (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- The native constant-ring inverse image has the original abelian inverse image underneath. -/
def moduleInverseImageUnderlyingIso :
    moduleInverseImage F J K Λ ⋙ SheafOfModules.toSheaf (constantRing K Λ) ≅
      SheafOfModules.toSheaf (constantRing J Λ) ⋙ F.sheafPullback AddCommGrpCat.{w} J K :=
  Functor.isoWhiskerRight (moduleInverseImageTransportIso F J K Λ)
    (SheafOfModules.toSheaf (constantRing K Λ)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      ((moduleSheafEquivalence J Λ).inverse ⋙ moduleValuedInverseImage F J K Λ)
      (moduleSheafUnderlyingIso K Λ) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleSheafEquivalence J Λ).inverse
      (moduleValuedInverseImageUnderlyingIso F J K Λ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleSheafInverseUnderlyingIso J Λ)
      (F.sheafPullback AddCommGrpCat.{w} J K)

/-- The actual underlying inverse-image comparison retains its seven original factors. -/
theorem moduleInverseImageUnderlyingIso_eq_original :
    moduleInverseImageUnderlyingIso F J K Λ =
      Functor.isoWhiskerRight (moduleInverseImageTransportIso F J K Λ)
        (SheafOfModules.toSheaf (constantRing K Λ)) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        ((moduleSheafEquivalence J Λ).inverse ⋙ moduleValuedInverseImage F J K Λ)
        (moduleSheafUnderlyingIso K Λ) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (moduleSheafEquivalence J Λ).inverse
        (moduleValuedInverseImageUnderlyingIso F J K Λ) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (moduleSheafInverseUnderlyingIso J Λ)
        (F.sheafPullback AddCommGrpCat.{w} J K) := rfl

/-- The fixed native inverse-image comparison preserves the original native
unit and the original abelian unit. -/
private theorem moduleInverseImageUnderlyingIso_unit_calc
    (M : ModuleSheaf.{u₁, v₁, r, w} J Λ) :
    (SheafOfModules.toSheaf (constantRing J Λ)).map
        ((moduleInverseImageAdjunction F J K Λ).unit.app M) ≫
      (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map
        ((moduleInverseImageUnderlyingIso F J K Λ).hom.app M) =
    (F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app
      ((SheafOfModules.toSheaf (constantRing J Λ)).obj M) := by
  have hu := congrArg (SheafOfModules.toSheaf (constantRing J Λ)).map
    (moduleInverseImageTransportIso_unit_app F J K Λ M)
  simp only [Functor.map_comp] at hu
  change (SheafOfModules.toSheaf (constantRing J Λ)).map
      ((moduleInverseImageAdjunction F J K Λ).unit.app M) ≫
    (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map
      ((SheafOfModules.toSheaf (constantRing K Λ)).map
      ((moduleInverseImageTransportIso F J K Λ).hom.app M)) =
    (SheafOfModules.toSheaf (constantRing J Λ)).map
      ((moduleTransportAdjunction F J K Λ).unit.app M) at hu
  have he : (moduleInverseImageUnderlyingIso F J K Λ).hom.app M =
      (SheafOfModules.toSheaf (constantRing K Λ)).map
        ((moduleInverseImageTransportIso F J K Λ).hom.app M) ≫
      (moduleSheafUnderlyingIso K Λ).hom.app
        ((moduleValuedInverseImage F J K Λ).obj
          ((moduleSheafEquivalence J Λ).inverse.obj M)) ≫
      (moduleValuedInverseImageUnderlyingIso F J K Λ).hom.app
        ((moduleSheafEquivalence J Λ).inverse.obj M) := by
    unfold moduleInverseImageUnderlyingIso
    rw [moduleSheafInverseUnderlyingIso_eq_refl]
    exact Functor.underlyingComparison_hom_app
      (moduleSheafEquivalence J Λ).inverse (moduleValuedInverseImage F J K Λ)
      (moduleSheafEquivalence K Λ).functor (SheafOfModules.toSheaf (constantRing K Λ))
      (sheafCompose K
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}))
      (sheafCompose J
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}))
      (F.sheafPullback AddCommGrpCat.{w} J K) (moduleInverseImage F J K Λ)
      (moduleInverseImageTransportIso F J K Λ)
      (moduleSheafUnderlyingIso K Λ) (moduleValuedInverseImageUnderlyingIso F J K Λ) M
  have hh := congrArg (fun z =>
    (SheafOfModules.toSheaf (constantRing J Λ)).map
      ((moduleInverseImageAdjunction F J K Λ).unit.app M) ≫
        (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map z) he
  let x := (SheafOfModules.toSheaf (constantRing K Λ)).map
    ((moduleInverseImageTransportIso F J K Λ).hom.app M)
  let y := (moduleSheafUnderlyingIso K Λ).hom.app
    ((moduleValuedInverseImage F J K Λ).obj
      ((moduleSheafEquivalence J Λ).inverse.obj M))
  let z := (moduleValuedInverseImageUnderlyingIso F J K Λ).hom.app
    ((moduleSheafEquivalence J Λ).inverse.obj M)
  have hmap := ((F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map_comp x (y ≫ z)).trans
    (congrArg (fun q => (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map x ≫ q)
      ((F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map_comp y z))
  have hh' := hh.trans (congrArg (fun q =>
    (SheafOfModules.toSheaf (constantRing J Λ)).map
      ((moduleInverseImageAdjunction F J K Λ).unit.app M) ≫ q) hmap)
  have ht := moduleTransportAdjunction_unit_underlying F J K Λ M
  have hv := moduleValuedInverseImageUnderlyingIso_unit F J K Λ
    ((moduleSheafEquivalence J Λ).inverse.obj M)
  exact hh'.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ _ ≫ _) hu).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ _) ht).trans hv))))

/-- The WHOLE actual native inverse-image comparison preserves the original abelian unit. -/
theorem moduleInverseImageUnderlyingIso_unit :
    (Functor.leftUnitor (SheafOfModules.toSheaf.{w} (constantRing J Λ))).inv ≫
      Functor.whiskerRight (moduleInverseImageAdjunction F J K Λ).unit
        (SheafOfModules.toSheaf.{w} (constantRing J Λ)) ≫
      (Functor.associator (moduleInverseImage F J K Λ) (moduleDirectImage F J K Λ)
        (SheafOfModules.toSheaf.{w} (constantRing J Λ))).hom ≫
      Functor.whiskerLeft (moduleInverseImage F J K Λ)
        (moduleDirectImageUnderlyingIso F J K Λ).hom ≫
      (Functor.associator (moduleInverseImage F J K Λ)
        (SheafOfModules.toSheaf.{w} (constantRing K Λ))
        (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K)).inv ≫
      Functor.whiskerRight (moduleInverseImageUnderlyingIso F J K Λ).hom
        (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K) ≫
      (Functor.associator (SheafOfModules.toSheaf.{w} (constantRing J Λ))
        (F.sheafPullback AddCommGrpCat.{w} J K)
        (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K)).hom =
      (Functor.rightUnitor (SheafOfModules.toSheaf.{w} (constantRing J Λ))).inv ≫
        Functor.whiskerLeft (SheafOfModules.toSheaf.{w} (constantRing J Λ))
          (F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit := by
  apply NatTrans.ext
  funext M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_inv_app, moduleDirectImageUnderlyingIso_hom_app_value,
    Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id]
  exact insert_id_comp_value
    (A := (SheafOfModules.toSheaf.{w} (constantRing J Λ)).obj M)
    (B := (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj
      ((SheafOfModules.toSheaf.{w} (constantRing K Λ)).obj
        ((moduleInverseImage F J K Λ).obj M)))
    (C := (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj
      ((F.sheafPullback AddCommGrpCat.{w} J K).obj
        ((SheafOfModules.toSheaf.{w} (constantRing J Λ)).obj M))) _ _ _
    (moduleInverseImageUnderlyingIso_unit_calc F J K Λ M)

/-- The component of the whole original-unit comparison at an actual module sheaf. -/
@[reassoc]
theorem moduleInverseImageUnderlyingIso_unit_app (M : ModuleSheaf.{u₁, v₁, r, w} J Λ) :
    (SheafOfModules.toSheaf (constantRing J Λ)).map
        ((moduleInverseImageAdjunction F J K Λ).unit.app M) ≫
      (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map
        ((moduleInverseImageUnderlyingIso F J K Λ).hom.app M) =
    (F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app
      ((SheafOfModules.toSheaf (constantRing J Λ)).obj M) := by
  have h := NatTrans.congr_app (moduleInverseImageUnderlyingIso_unit F J K Λ) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_inv_app, moduleDirectImageUnderlyingIso_hom_app_value,
    Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id] at h
  exact remove_id_comp_value
    (A := (SheafOfModules.toSheaf.{w} (constantRing J Λ)).obj M)
    (B := (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj
      ((SheafOfModules.toSheaf.{w} (constantRing K Λ)).obj
        ((moduleInverseImage F J K Λ).obj M)))
    (C := (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj
      ((F.sheafPullback AddCommGrpCat.{w} J K).obj
        ((SheafOfModules.toSheaf.{w} (constantRing J Λ)).obj M))) _ _ _ h

/-- The inverse of the fixed native pullback comparison has the original
direct-image comparison as its mate. -/
theorem mate_moduleInverseImageUnderlyingIso_inv :
    (mateEquiv (moduleInverseImageAdjunction F J K Λ)
      (F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K)
      (TwoSquare.mk _ _ _ _ (moduleInverseImageUnderlyingIso F J K Λ).inv)).natTrans =
        (moduleDirectImageUnderlyingIso F J K Λ).hom := by
  apply mateEquiv_inv_natTrans_eq_of_unit (moduleInverseImageAdjunction F J K Λ)
    (F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K) (moduleInverseImageUnderlyingIso F J K Λ)
    (moduleDirectImageUnderlyingIso F J K Λ).hom
  intro M
  exact (congrArg (fun z => (SheafOfModules.toSheaf (constantRing J Λ)).map
      ((moduleInverseImageAdjunction F J K Λ).unit.app M) ≫ z)
    (Category.id_comp ((F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map
      ((moduleInverseImageUnderlyingIso F J K Λ).hom.app M)))).trans
        (moduleInverseImageUnderlyingIso_unit_app F J K Λ M)

end Images

end ModuleCat.Sheaf.ConstantRing
