/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Images

/-! # Native inverse image of constant ring sheaves

Terminal-object preservation identifies the two native constant-sheaf
adjunctions after composition with the actual site adjunction. Their comparison
has exactly the previously constructed constant-ring morphism as its transpose.
Site object, site morphism and ring universes remain independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat.Sheaf.ConstantRing

private theorem constantSheafAdj_unit_value {C : Type*} [Category* C]
    {A : Type*} [Category* A] (J : GrothendieckTopology C) [HasWeakSheafify J A]
    {T : C} (hT : IsTerminal T) (X : A) :
    (constantSheafAdj J A hT).unit.app X =
      (toSheafify J ((Functor.const Cᵒᵖ).obj X)).app (op T) := by
  rw [constantSheafAdj, Adjunction.comp_unit_app, constantPresheafAdj_unit_app,
    Category.id_comp]
  rfl

private theorem constantSheafAdj_homEquiv_value {C : Type*} [Category* C]
    {A : Type*} [Category* A] (J : GrothendieckTopology C) [HasWeakSheafify J A]
    {T : C} (hT : IsTerminal T) (X : A) (M : Sheaf J A)
    (a : (constantSheaf J A).obj X ⟶ M) :
    (constantSheafAdj J A hT).homEquiv X M a =
      (toSheafify J ((Functor.const Cᵒᵖ).obj X) ≫ a.hom).app (op T) := by
  rw [Adjunction.homEquiv_unit, constantSheafAdj_unit_value]
  rfl

universe u₁ v₁ u₂ v₂ r

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K]
  [HasWeakSheafify J RingCat.{r}] [HasWeakSheafify K RingCat.{r}]
  [(F.sheafPushforwardContinuous RingCat.{r} J K).IsRightAdjoint]
  (T : C) (hT : IsTerminal T) (hFT : IsTerminal (F.obj T))

/-- Native ring-valued inverse image of the whole constant-sheaf family. -/
def constantRingPullbackFamilyIso :
    constantSheaf J RingCat.{r} ⋙ F.sheafPullback RingCat.{r} J K ≅
      constantSheaf K RingCat.{r} :=
  ((constantSheafAdj J RingCat.{r} hT).comp
    (F.sheafAdjunctionContinuous RingCat.{r} J K)).leftAdjointUniq
      (constantSheafAdj K RingCat.{r} hFT)

/-- The family retains the original native adjoint-uniqueness construction. -/
theorem constantRingPullbackFamilyIso_eq_original :
    constantRingPullbackFamilyIso F J K T hT hFT =
      ((constantSheafAdj J RingCat.{r} hT).comp
        (F.sheafAdjunctionContinuous RingCat.{r} J K)).leftAdjointUniq
          (constantSheafAdj K RingCat.{r} hFT) := rfl

/-- The whole constant-ring family preserves the original composite adjunction unit. -/
theorem constantRingPullbackFamilyIso_unit :
    ((constantSheafAdj J RingCat.{r} hT).comp
        (F.sheafAdjunctionContinuous RingCat.{r} J K)).unit ≫
      Functor.whiskerRight (constantRingPullbackFamilyIso F J K T hT hFT).hom
        ((sheafSections K RingCat.{r}).obj (op (F.obj T))) =
      (constantSheafAdj K RingCat.{r} hFT).unit :=
  Adjunction.unit_leftAdjointUniq_hom _ _

/-- The whole constant-ring family preserves the original composite adjunction counit. -/
theorem constantRingPullbackFamilyIso_counit :
    Functor.whiskerLeft ((sheafSections K RingCat.{r}).obj (op (F.obj T)))
        (constantRingPullbackFamilyIso F J K T hT hFT).hom ≫
      (constantSheafAdj K RingCat.{r} hFT).counit =
      ((constantSheafAdj J RingCat.{r} hT).comp
        (F.sheafAdjunctionContinuous RingCat.{r} J K)).counit :=
  Adjunction.leftAdjointUniq_hom_counit _ _

variable (Λ : Type r) [Ring Λ]

/-- Native pullback of the associated constant ring, at its original coefficient ring. -/
def constantRingPullbackIso :
    (F.sheafPullback RingCat.{r} J K).obj (constantRing J Λ) ≅ constantRing K Λ :=
  (constantRingPullbackFamilyIso F J K T hT hFT).app (RingCat.of Λ)

/-- The object comparison is the original whole native comparison at `RingCat.of Λ`. -/
theorem constantRingPullbackIso_eq_original :
    constantRingPullbackIso F J K T hT hFT Λ =
      (((constantSheafAdj J RingCat.{r} hT).comp
        (F.sheafAdjunctionContinuous RingCat.{r} J K)).leftAdjointUniq
          (constantSheafAdj K RingCat.{r} hFT)).app (RingCat.of Λ) := rfl

/-- The actual comparison transposes to the already constructed constant-ring morphism. -/
theorem constantRingPullbackIso_adjoint :
    (F.sheafAdjunctionContinuous RingCat.{r} J K).homEquiv
        (constantRing J Λ) (constantRing K Λ)
        (constantRingPullbackIso F J K T hT hFT Λ).hom =
      constantRingMap F J K Λ := by
  apply ((constantSheafAdj J RingCat.{r} hT).homEquiv (RingCat.of Λ)
    ((F.sheafPushforwardContinuous RingCat.{r} J K).obj (constantRing K Λ))).injective
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((constantSheafAdj J RingCat.{r} hT).comp
      (F.sheafAdjunctionContinuous RingCat.{r} J K))
    (constantSheafAdj K RingCat.{r} hFT) (RingCat.of Λ)
  rw [Adjunction.comp_homEquiv] at h
  change (constantSheafAdj J RingCat.{r} hT).homEquiv (RingCat.of Λ)
      ((F.sheafPushforwardContinuous RingCat.{r} J K).obj (constantRing K Λ))
      ((F.sheafAdjunctionContinuous RingCat.{r} J K).homEquiv
        (constantRing J Λ) (constantRing K Λ)
        (constantRingPullbackIso F J K T hT hFT Λ).hom) =
    (constantSheafAdj K RingCat.{r} hFT).unit.app (RingCat.of Λ) at h
  refine h.trans ?_
  exact (constantSheafAdj_unit_value K hFT (RingCat.of Λ)).trans
    ((constantRingUnit_comp_constantRingMap_app F J K Λ (op T)).symm.trans
      (constantSheafAdj_homEquiv_value J hT (RingCat.of Λ)
        ((F.sheafPushforwardContinuous RingCat.{r} J K).obj (constantRing K Λ))
        (constantRingMap F J K Λ)).symm)

/-- The actual native site unit factors through the original constant-ring morphism. -/
@[reassoc]
theorem constantRingPullbackIso_unit :
    (F.sheafAdjunctionContinuous RingCat.{r} J K).unit.app (constantRing J Λ) ≫
      (F.sheafPushforwardContinuous RingCat.{r} J K).map
        (constantRingPullbackIso F J K T hT hFT Λ).hom =
      constantRingMap F J K Λ :=
  constantRingPullbackIso_adjoint F J K T hT hFT Λ

/-- The comparison is the original ring morphism transposed by the actual native counit. -/
theorem constantRingPullbackIso_hom_eq_counit :
    (constantRingPullbackIso F J K T hT hFT Λ).hom =
      (F.sheafPullback RingCat.{r} J K).map (constantRingMap F J K Λ) ≫
        (F.sheafAdjunctionContinuous RingCat.{r} J K).counit.app (constantRing K Λ) := by
  have h := congrArg
    ((F.sheafAdjunctionContinuous RingCat.{r} J K).homEquiv
      (constantRing J Λ) (constantRing K Λ)).symm
    (constantRingPullbackIso_adjoint F J K T hT hFT Λ)
  simpa only [Equiv.symm_apply_apply, Adjunction.homEquiv_counit] using h

/-- The whole original ring sheafification unit factors through the native comparison. -/
@[reassoc]
theorem constantRingPullbackIso_ringUnit :
    constantRingUnit J Λ ≫
      ((F.sheafAdjunctionContinuous RingCat.{r} J K).unit.app (constantRing J Λ) ≫
        (F.sheafPushforwardContinuous RingCat.{r} J K).map
          (constantRingPullbackIso F J K T hT hFT Λ).hom).hom =
      Functor.whiskerLeft F.op (constantRingUnit K Λ) := by
  rw [constantRingPullbackIso_unit]
  exact constantRingUnit_comp_constantRingMap F J K Λ

/-- Every original ring-unit component retains the actual native unit and comparison maps. -/
@[reassoc]
theorem constantRingPullbackIso_ringUnit_app (U : Cᵒᵖ) :
    (constantRingUnit J Λ).app U ≫
      ((F.sheafAdjunctionContinuous RingCat.{r} J K).unit.app
        (constantRing J Λ)).hom.app U ≫
      (constantRingPullbackIso F J K T hT hFT Λ).hom.hom.app (F.op.obj U) =
      (constantRingUnit K Λ).app (F.op.obj U) :=
  NatTrans.congr_app (constantRingPullbackIso_ringUnit F J K T hT hFT Λ) U

end ModuleCat.Sheaf.ConstantRing
