/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Pullback

/-! # Original constant-ring image identity and composition comparisons

Actual isomorphisms of site functors supply the native module-valued
comparisons. Fully faithful coefficient transport constructs the genuine
ringed comparisons, and the original adjunctions construct their inverse
image comparisons. Whole unit and counit equations retain those values.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.Sheaf.ConstantRing

universe u₁ v₁ u₂ v₂ u₃ v₃ r w

section Composition

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  (Λ : Type r) [Ring Λ] [F.IsContinuous J K] [G.IsContinuous K L] [H.IsContinuous J L]

/-- The actual module-valued composition comparison for the supplied site-functor isomorphism. -/
def moduleValuedDirectImageCompIso (e : F ⋙ G ≅ H) :
    moduleValuedDirectImage H J L Λ ≅
      moduleValuedDirectImage G K L Λ ⋙ moduleValuedDirectImage F J K Λ :=
  (Functor.sheafPushforwardContinuousComp' e (ModuleCat.{w} Λ) J K L).symm

variable [HasWeakSheafify J RingCat.{r}] [HasWeakSheafify K RingCat.{r}]
  [HasWeakSheafify L RingCat.{r}]
  [J.WEqualsLocallyBijective RingCat.{r}] [K.WEqualsLocallyBijective RingCat.{r}]
  [L.WEqualsLocallyBijective RingCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]
  [HasWeakSheafify L AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [L.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [L.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- Whole direct-image composition after the original inverse coefficient equivalence. -/
def moduleDirectImageCompRightIso :
    (moduleDirectImage G K L Λ ⋙ moduleDirectImage F J K Λ) ⋙
        (moduleSheafEquivalence J Λ).inverse ≅
      (moduleSheafEquivalence L Λ).inverse ⋙
        moduleValuedDirectImage G K L Λ ⋙ moduleValuedDirectImage F J K Λ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (moduleDirectImageComparison F J K Λ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleDirectImageComparison G K L Λ) _ ≪≫
    Functor.associator _ _ _

/-- Genuine ringed direct-image composition constructed from the actual site comparison. -/
def moduleDirectImageCompIso (e : F ⋙ G ≅ H) :
    moduleDirectImage H J L Λ ≅ moduleDirectImage G K L Λ ⋙ moduleDirectImage F J K Λ :=
  ((Functor.whiskeringRight (ModuleSheaf.{u₃, v₃, r, w} L Λ)
    (ModuleSheaf.{u₁, v₁, r, w} J Λ) (ModuleValuedSheaf.{u₁, v₁, r, w} J Λ)).obj
      (moduleSheafEquivalence J Λ).inverse).preimageIso
    (moduleDirectImageComparison H J L Λ ≪≫
      Functor.isoWhiskerLeft _ (moduleValuedDirectImageCompIso F G H J K L Λ e) ≪≫
      (moduleDirectImageCompRightIso F G J K L Λ).symm)

/-- The native ringed composition has exactly its original whole module-valued comparison. -/
theorem moduleDirectImageCompIso_whisker (e : F ⋙ G ≅ H) :
    Functor.isoWhiskerRight (moduleDirectImageCompIso F G H J K L Λ e)
        (moduleSheafEquivalence J Λ).inverse =
      moduleDirectImageComparison H J L Λ ≪≫
        Functor.isoWhiskerLeft _ (moduleValuedDirectImageCompIso F G H J K L Λ e) ≪≫
        (moduleDirectImageCompRightIso F G J K L Λ).symm := by
  apply Iso.ext
  exact ((Functor.whiskeringRight (ModuleSheaf.{u₃, v₃, r, w} L Λ)
    (ModuleSheaf.{u₁, v₁, r, w} J Λ) (ModuleValuedSheaf.{u₁, v₁, r, w} J Λ)).obj
      (moduleSheafEquivalence J Λ).inverse).map_preimage _

/-- Every original section map in the inverse comparison is the supplied site-isomorphism map. -/
theorem moduleDirectImageCompIso_inv_app_apply (e : F ⋙ G ≅ H)
    (M : ModuleSheaf.{u₃, v₃, r, w} L Λ) (U : Cᵒᵖ)
    (x : M.val.obj (G.op.obj (F.op.obj U))) :
    (((moduleDirectImageCompIso F G H J K L Λ e).inv.app M).val.app U) x =
      M.val.map ((e.inv.app U.unop).op) x := by
  let W := (Functor.whiskeringRight (ModuleSheaf.{u₃, v₃, r, w} L Λ)
    (ModuleSheaf.{u₁, v₁, r, w} J Λ) (ModuleValuedSheaf.{u₁, v₁, r, w} J Λ)).obj
      (moduleSheafEquivalence J Λ).inverse
  have h := W.map_preimage
    (moduleDirectImageComparison H J L Λ ≪≫
      Functor.isoWhiskerLeft _ (moduleValuedDirectImageCompIso F G H J K L Λ e) ≪≫
      (moduleDirectImageCompRightIso F G J K L Λ).symm).inv
  exact congrArg (fun a => (((a.app M).hom.app U).hom x)) h

section InverseImage

variable [∀ P : Cᵒᵖ ⥤ ModuleCat.{w} Λ, F.op.HasLeftKanExtension P]
  [∀ P : Dᵒᵖ ⥤ ModuleCat.{w} Λ, G.op.HasLeftKanExtension P]
  [∀ P : Cᵒᵖ ⥤ ModuleCat.{w} Λ, H.op.HasLeftKanExtension P]
  [HasWeakSheafify K (ModuleCat.{w} Λ)] [HasWeakSheafify L (ModuleCat.{w} Λ)]

/-- Native inverse-image composition fixed by the original three adjunctions. -/
def moduleInverseImageCompIso (e : F ⋙ G ≅ H) :
    moduleInverseImage H J L Λ ≅ moduleInverseImage F J K Λ ⋙ moduleInverseImage G K L Λ :=
  ((moduleInverseImageAdjunction H J L Λ).ofNatIsoRight
    (moduleDirectImageCompIso F G H J K L Λ e)).leftAdjointUniq
      ((moduleInverseImageAdjunction F J K Λ).comp (moduleInverseImageAdjunction G K L Λ))

/-- The whole inverse-image composition preserves the original composite adjunction unit. -/
theorem moduleInverseImageCompIso_unit (e : F ⋙ G ≅ H) :
    (moduleInverseImageAdjunction H J L Λ).unit ≫
      Functor.whiskerRight (moduleInverseImageCompIso F G H J K L Λ e).hom
        (moduleDirectImage H J L Λ) ≫
      Functor.whiskerLeft (moduleInverseImage F J K Λ ⋙ moduleInverseImage G K L Λ)
        (moduleDirectImageCompIso F G H J K L Λ e).hom =
      ((moduleInverseImageAdjunction F J K Λ).comp
        (moduleInverseImageAdjunction G K L Λ)).unit := by
  have h := Adjunction.unit_leftAdjointUniq_hom
    ((moduleInverseImageAdjunction H J L Λ).ofNatIsoRight
      (moduleDirectImageCompIso F G H J K L Λ e))
    ((moduleInverseImageAdjunction F J K Λ).comp (moduleInverseImageAdjunction G K L Λ))
  simpa only [moduleInverseImageCompIso, Adjunction.ofNatIsoRight_unit, Category.assoc,
    Functor.whiskerLeft_comp_whiskerRight] using h

/-- The whole inverse-image composition preserves the original composite adjunction counit. -/
theorem moduleInverseImageCompIso_counit (e : F ⋙ G ≅ H) :
    Functor.whiskerLeft (moduleDirectImage G K L Λ ⋙ moduleDirectImage F J K Λ)
        (moduleInverseImageCompIso F G H J K L Λ e).hom ≫
      ((moduleInverseImageAdjunction F J K Λ).comp
        (moduleInverseImageAdjunction G K L Λ)).counit =
      Functor.whiskerRight (moduleDirectImageCompIso F G H J K L Λ e).inv
        (moduleInverseImage H J L Λ) ≫
      (moduleInverseImageAdjunction H J L Λ).counit := by
  simpa only [moduleInverseImageCompIso, Adjunction.ofNatIsoRight_counit] using
    Adjunction.leftAdjointUniq_hom_counit
      ((moduleInverseImageAdjunction H J L Λ).ofNatIsoRight
        (moduleDirectImageCompIso F G H J K L Λ e))
      ((moduleInverseImageAdjunction F J K Λ).comp (moduleInverseImageAdjunction G K L Λ))

end InverseImage

end Composition

section Identity

variable {C : Type u₁} [Category.{v₁} C] (F : C ⥤ C) (J : GrothendieckTopology C)
  (Λ : Type r) [Ring Λ] [F.IsContinuous J J]

/-- Module-valued identity from the actual identity comparison of site functors. -/
def moduleValuedDirectImageIdIso (e : F ≅ 𝟭 C) :
    moduleValuedDirectImage F J J Λ ≅ 𝟭 (ModuleValuedSheaf.{u₁, v₁, r, w} J Λ) :=
  Functor.sheafPushforwardContinuousId' e (ModuleCat.{w} Λ) J

variable [HasWeakSheafify J RingCat.{r}] [J.WEqualsLocallyBijective RingCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- Native direct-image identity after the original inverse coefficient equivalence. -/
def moduleDirectImageIdValuedIso (e : F ≅ 𝟭 C) :
    moduleDirectImage F J J Λ ⋙ (moduleSheafEquivalence J Λ).inverse ≅
      (𝟭 (ModuleSheaf.{u₁, v₁, r, w} J Λ)) ⋙ (moduleSheafEquivalence J Λ).inverse :=
  moduleDirectImageComparison F J J Λ ≪≫
    Functor.isoWhiskerLeft _ (moduleValuedDirectImageIdIso F J Λ e) ≪≫
    Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm

/-- Native direct-image identity determined by its original module-valued comparison. -/
def moduleDirectImageIdIso (e : F ≅ 𝟭 C) :
    moduleDirectImage F J J Λ ≅ 𝟭 (ModuleSheaf.{u₁, v₁, r, w} J Λ) :=
  ((Functor.whiskeringRight (ModuleSheaf.{u₁, v₁, r, w} J Λ)
    (ModuleSheaf.{u₁, v₁, r, w} J Λ) (ModuleValuedSheaf.{u₁, v₁, r, w} J Λ)).obj
      (moduleSheafEquivalence J Λ).inverse).preimageIso (moduleDirectImageIdValuedIso F J Λ e)

variable [∀ P : Cᵒᵖ ⥤ ModuleCat.{w} Λ, F.op.HasLeftKanExtension P]
  [HasWeakSheafify J (ModuleCat.{w} Λ)]

/-- Native inverse-image identity with the original adjunction normalization. -/
def moduleInverseImageIdIso (e : F ≅ 𝟭 C) :
    moduleInverseImage F J J Λ ≅ 𝟭 (ModuleSheaf.{u₁, v₁, r, w} J Λ) :=
  ((moduleInverseImageAdjunction F J J Λ).ofNatIsoRight
    (moduleDirectImageIdIso F J Λ e)).leftAdjointUniq Adjunction.id

/-- Whole identity compatibility retains the original transported unit. -/
theorem moduleInverseImageIdIso_unit (e : F ≅ 𝟭 C) :
    ((moduleInverseImageAdjunction F J J Λ).ofNatIsoRight
      (moduleDirectImageIdIso F J Λ e)).unit ≫
      Functor.whiskerRight (moduleInverseImageIdIso F J Λ e).hom (𝟭 _) =
      Adjunction.id.unit :=
  Adjunction.unit_leftAdjointUniq_hom _ _

/-- Whole identity compatibility retains the original transported counit. -/
theorem moduleInverseImageIdIso_counit (e : F ≅ 𝟭 C) :
    Functor.whiskerLeft (𝟭 _) (moduleInverseImageIdIso F J Λ e).hom ≫ Adjunction.id.counit =
      ((moduleInverseImageAdjunction F J J Λ).ofNatIsoRight
        (moduleDirectImageIdIso F J Λ e)).counit :=
  Adjunction.leftAdjointUniq_hom_counit _ _

end Identity

end ModuleCat.Sheaf.ConstantRing
