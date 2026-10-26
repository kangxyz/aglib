/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Pullback

/-! # Actual constant-ring morphisms and direct images on arbitrary sites

The ring morphism is the extension of the original target sheafification unit.
Ringed direct image is the native module pushforward along this morphism;
module-valued direct image is the native continuous-site pushforward.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.Sheaf.ConstantRing

universe u₁ v₁ u₂ v₂ u₃ v₃ r w

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (Λ : Type r) [Ring Λ] [F.IsContinuous J K]

/-- Native direct image of sheaves valued in modules over the original ring. -/
abbrev moduleValuedDirectImage :
    ModuleValuedSheaf.{u₂, v₂, r, w} K Λ ⥤ ModuleValuedSheaf.{u₁, v₁, r, w} J Λ :=
  F.sheafPushforwardContinuous (ModuleCat.{w} Λ) J K

variable [HasWeakSheafify J RingCat.{r}] [HasWeakSheafify K RingCat.{r}]

/-- The actual constant ring morphism along the original continuous site functor. -/
def constantRingMap : constantRing J Λ ⟶
    (F.sheafPushforwardContinuous RingCat.{r} J K).obj (constantRing K Λ) :=
  ⟨CategoryTheory.sheafifyLift J (Functor.whiskerLeft F.op (constantRingUnit K Λ))
    ((F.sheafPushforwardContinuous RingCat.{r} J K).obj (constantRing K Λ)).property⟩

/-- The ring morphism retains the original native sheafification lift. -/
theorem constantRingMap_eq_original :
    constantRingMap F J K Λ =
      ⟨CategoryTheory.sheafifyLift J (Functor.whiskerLeft F.op (constantRingUnit K Λ))
        ((F.sheafPushforwardContinuous RingCat.{r} J K).obj (constantRing K Λ)).property⟩ :=
  rfl

/-- The whole original ring unit factors through the actual constant-ring morphism. -/
@[reassoc]
theorem constantRingUnit_comp_constantRingMap :
    constantRingUnit J Λ ≫ (constantRingMap F J K Λ).hom =
      Functor.whiskerLeft F.op (constantRingUnit K Λ) :=
  CategoryTheory.toSheafify_sheafifyLift _ _ _

/-- The component of the whole ring-unit factorization. -/
@[reassoc]
theorem constantRingUnit_comp_constantRingMap_app (U : Cᵒᵖ) :
    (constantRingUnit J Λ).app U ≫ (constantRingMap F J K Λ).hom.app U =
      (constantRingUnit K Λ).app (F.op.obj U) :=
  NatTrans.congr_app (constantRingUnit_comp_constantRingMap F J K Λ) U

/-- Genuine native ringed direct image over the original constant-ring morphism. -/
def moduleDirectImage :
    ModuleSheaf.{u₂, v₂, r, w} K Λ ⥤ ModuleSheaf.{u₁, v₁, r, w} J Λ :=
  SheafOfModules.pushforward (constantRingMap F J K Λ)

/-- The direct-image constructor is the original native module pushforward. -/
theorem moduleDirectImage_eq_original :
    moduleDirectImage F J K Λ = SheafOfModules.pushforward (constantRingMap F J K Λ) := rfl

/-- Ringed direct image retains the original continuous abelian direct image. -/
def moduleDirectImageUnderlyingIso :
    moduleDirectImage F J K Λ ⋙ SheafOfModules.toSheaf (constantRing J Λ) ≅
      SheafOfModules.toSheaf (constantRing K Λ) ⋙
        F.sheafPushforwardContinuous AddCommGrpCat.{w} J K :=
  Iso.refl _

omit F K [F.IsContinuous J K] [HasWeakSheafify K RingCat.{r}] in
/-- The original constant-ring morphism for the identity functor is identity. -/
theorem constantRingMap_id : constantRingMap (𝟭 C) J J Λ = 𝟙 (constantRing J Λ) := by
  apply ((sheafificationAdjunction J RingCat.{r}).homEquiv _ _).injective
  change constantRingUnit J Λ ≫ (constantRingMap (𝟭 C) J J Λ).hom =
    constantRingUnit J Λ ≫ 𝟙 _
  rw [constantRingUnit_comp_constantRingMap, Category.comp_id]
  rfl

omit F K [F.IsContinuous J K] [HasWeakSheafify K RingCat.{r}] in
/-- Identity direct image uses the original native ringed identity comparison. -/
def moduleDirectImageId : moduleDirectImage (𝟭 C) J J Λ ≅ 𝟭 (ModuleSheaf J Λ) :=
  SheafOfModules.pushforwardCongr (constantRingMap_id J Λ) ≪≫
    SheafOfModules.pushforwardId (constantRing J Λ)

section Composition

variable {E : Type u₃} [Category.{v₃} E] (G : D ⥤ E) (L : GrothendieckTopology E)
  [G.IsContinuous K L] [HasWeakSheafify L RingCat.{r}]

/-- The whole constant-ring morphism respects the original composition of site functors. -/
theorem constantRingMap_comp :
    letI : (F ⋙ G).IsContinuous J L := Functor.isContinuous_comp F G J K L
    constantRingMap (F ⋙ G) J L Λ =
      constantRingMap F J K Λ ≫
        (F.sheafPushforwardContinuous RingCat.{r} J K).map (constantRingMap G K L Λ) := by
  let : (F ⋙ G).IsContinuous J L := Functor.isContinuous_comp F G J K L
  apply ((sheafificationAdjunction J RingCat.{r}).homEquiv _ _).injective
  change constantRingUnit J Λ ≫ (constantRingMap (F ⋙ G) J L Λ).hom =
    constantRingUnit J Λ ≫ ((constantRingMap F J K Λ).hom ≫
      Functor.whiskerLeft F.op (constantRingMap G K L Λ).hom)
  rw [constantRingUnit_comp_constantRingMap, ← Category.assoc,
    constantRingUnit_comp_constantRingMap, ← Functor.whiskerLeft_comp,
    constantRingUnit_comp_constantRingMap]
  rfl

/-- Native module-valued direct images compose through the original site functors. -/
def moduleValuedDirectImageComp :
    letI : (F ⋙ G).IsContinuous J L := Functor.isContinuous_comp F G J K L
    moduleValuedDirectImage G K L Λ ⋙ moduleValuedDirectImage F J K Λ ≅
      moduleValuedDirectImage (F ⋙ G) J L Λ := by
  let : (F ⋙ G).IsContinuous J L := Functor.isContinuous_comp F G J K L
  exact Functor.sheafPushforwardContinuousComp F G (ModuleCat.{w} Λ) J K L

/-- Native ringed direct images compose through the original constant-ring morphisms. -/
def moduleDirectImageComp :
    letI : (F ⋙ G).IsContinuous J L := Functor.isContinuous_comp F G J K L
    moduleDirectImage G K L Λ ⋙ moduleDirectImage F J K Λ ≅
      moduleDirectImage (F ⋙ G) J L Λ := by
  let : (F ⋙ G).IsContinuous J L := Functor.isContinuous_comp F G J K L
  exact SheafOfModules.pushforwardComp (constantRingMap F J K Λ) (constantRingMap G K L Λ) ≪≫
    SheafOfModules.pushforwardCongr (constantRingMap_comp F J K Λ G L).symm

end Composition

end ModuleCat.Sheaf.ConstantRing
