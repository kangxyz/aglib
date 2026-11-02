/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Pullback
public import Aglib.CategoryTheory.Adjunction.LeftAdjointComparison

/-! # Module-valued image comparisons without ring-sheaf size assumptions

These constructors retain a coefficient ring and module universe independently.
They do not require sheafification of rings in the coefficient ring universe.
Terminal data is used only for the constant-object comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.Sheaf.ConstantRing

universe u₁ v₁ u₂ v₂ u₃ v₃ r w

section Constants

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (Λ : Type r) [Ring Λ] [F.IsContinuous J K]
  [∀ P : Cᵒᵖ ⥤ ModuleCat.{w} Λ, F.op.HasLeftKanExtension P]
  [HasWeakSheafify J (ModuleCat.{w} Λ)] [HasWeakSheafify K (ModuleCat.{w} Λ)]
  (T : C) (hT : IsTerminal T) (hFT : IsTerminal (F.obj T))

/-- The actual constant-object inverse-image comparison from the two original adjunctions. -/
def moduleValuedInverseImageConstantIso :
    constantSheaf J (ModuleCat.{w} Λ) ⋙
        moduleValuedInverseImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ ≅
      constantSheaf K (ModuleCat.{w} Λ) :=
  ((constantSheafAdj J (ModuleCat.{w} Λ) hT).comp
    (moduleValuedInverseImageAdjunction F J K Λ)).leftAdjointUniq
      (constantSheafAdj K (ModuleCat.{w} Λ) hFT)

/-- The whole constant-object comparison preserves the original composed unit. -/
theorem moduleValuedInverseImageConstantIso_unit :
    ((constantSheafAdj J (ModuleCat.{w} Λ) hT).comp
        (moduleValuedInverseImageAdjunction F J K Λ)).unit ≫
      Functor.whiskerRight (moduleValuedInverseImageConstantIso F J K Λ T hT hFT).hom
        ((sheafSections K (ModuleCat.{w} Λ)).obj (.op (F.obj T))) =
      (constantSheafAdj K (ModuleCat.{w} Λ) hFT).unit :=
  Adjunction.unit_leftAdjointUniq_hom _ _

/-- The whole constant-object comparison preserves the original composed counit. -/
theorem moduleValuedInverseImageConstantIso_counit :
    Functor.whiskerLeft ((sheafSections K (ModuleCat.{w} Λ)).obj (.op (F.obj T)))
        (moduleValuedInverseImageConstantIso F J K Λ T hT hFT).hom ≫
      (constantSheafAdj K (ModuleCat.{w} Λ) hFT).counit =
      ((constantSheafAdj J (ModuleCat.{w} Λ) hT).comp
        (moduleValuedInverseImageAdjunction F J K Λ)).counit :=
  Adjunction.leftAdjointUniq_hom_counit _ _

end Constants

section Composition

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  (Λ : Type r) [Ring Λ] [F.IsContinuous J K] [G.IsContinuous K L] [H.IsContinuous J L]
  [∀ P : Cᵒᵖ ⥤ ModuleCat.{w} Λ, F.op.HasLeftKanExtension P]
  [∀ P : Dᵒᵖ ⥤ ModuleCat.{w} Λ, G.op.HasLeftKanExtension P]
  [∀ P : Cᵒᵖ ⥤ ModuleCat.{w} Λ, H.op.HasLeftKanExtension P]
  [HasWeakSheafify K (ModuleCat.{w} Λ)] [HasWeakSheafify L (ModuleCat.{w} Λ)]
  (e : F ⋙ G ≅ H)

/-- The original chosen module-valued inverse-image composition comparison. -/
def moduleValuedInverseImageCompIso :
    moduleValuedInverseImage.{u₁, v₁, u₃, v₃, r, w} H J L Λ ≅
      moduleValuedInverseImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ ⋙
        moduleValuedInverseImage.{u₂, v₂, u₃, v₃, r, w} G K L Λ :=
  (Adjunction.leftAdjointCompIso (moduleValuedInverseImageAdjunction F J K Λ)
    (moduleValuedInverseImageAdjunction G K L Λ)
    (moduleValuedInverseImageAdjunction H J L Λ)
    (Functor.sheafPushforwardContinuousComp' e (ModuleCat.{w} Λ) J K L)).symm

/-- Unit uniqueness reconciles the original composition comparison with right-adjoint transport. -/
theorem moduleValuedInverseImageCompIso_eq_unique :
    moduleValuedInverseImageCompIso F G H J K L Λ e =
      ((moduleValuedInverseImageAdjunction H J L Λ).ofNatIsoRight
        (Functor.sheafPushforwardContinuousComp' e (ModuleCat.{w} Λ) J K L).symm).leftAdjointUniq
      ((moduleValuedInverseImageAdjunction F J K Λ).comp
        (moduleValuedInverseImageAdjunction G K L Λ)) := by
  apply Iso.ext
  apply (conjugateEquiv
    ((moduleValuedInverseImageAdjunction F J K Λ).comp
      (moduleValuedInverseImageAdjunction G K L Λ))
    (moduleValuedInverseImageAdjunction H J L Λ)).injective
  have h₁ := Adjunction.conjugateEquiv_leftAdjointCompIso_inv
    (moduleValuedInverseImageAdjunction F J K Λ)
    (moduleValuedInverseImageAdjunction G K L Λ)
    (moduleValuedInverseImageAdjunction H J L Λ)
    (Functor.sheafPushforwardContinuousComp' e (ModuleCat.{w} Λ) J K L)
  have h₂ := conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
    (moduleValuedInverseImageAdjunction H J L Λ)
    ((moduleValuedInverseImageAdjunction F J K Λ).comp
      (moduleValuedInverseImageAdjunction G K L Λ))
    (Functor.sheafPushforwardContinuousComp' e (ModuleCat.{w} Λ) J K L).symm
  exact (show _ = _ from h₁).trans h₂.symm

/-- The whole module-valued composition comparison preserves the actual composed unit. -/
theorem moduleValuedInverseImageCompIso_unit :
    (moduleValuedInverseImageAdjunction H J L Λ).unit ≫
      Functor.whiskerRight (moduleValuedInverseImageCompIso F G H J K L Λ e).hom
        (moduleValuedDirectImage H J L Λ) ≫
      Functor.whiskerLeft (moduleValuedInverseImage F J K Λ ⋙ moduleValuedInverseImage G K L Λ)
        (Functor.sheafPushforwardContinuousComp' e (ModuleCat.{w} Λ) J K L).inv =
      ((moduleValuedInverseImageAdjunction F J K Λ).comp
        (moduleValuedInverseImageAdjunction G K L Λ)).unit := by
  rw [moduleValuedInverseImageCompIso_eq_unique]
  have h := Adjunction.unit_leftAdjointUniq_hom
    ((moduleValuedInverseImageAdjunction H J L Λ).ofNatIsoRight
      (Functor.sheafPushforwardContinuousComp' e (ModuleCat.{w} Λ) J K L).symm)
    ((moduleValuedInverseImageAdjunction F J K Λ).comp
      (moduleValuedInverseImageAdjunction G K L Λ))
  simpa only [Adjunction.ofNatIsoRight_unit, Category.assoc,
    Functor.whiskerLeft_comp_whiskerRight, Iso.symm_hom] using h

/-- The whole module-valued composition comparison preserves the actual composed counit. -/
theorem moduleValuedInverseImageCompIso_counit :
    Functor.whiskerLeft (moduleValuedDirectImage G K L Λ ⋙ moduleValuedDirectImage F J K Λ)
        (moduleValuedInverseImageCompIso F G H J K L Λ e).hom ≫
      ((moduleValuedInverseImageAdjunction F J K Λ).comp
        (moduleValuedInverseImageAdjunction G K L Λ)).counit =
      Functor.whiskerRight (Functor.sheafPushforwardContinuousComp' e
        (ModuleCat.{w} Λ) J K L).hom (moduleValuedInverseImage H J L Λ) ≫
      (moduleValuedInverseImageAdjunction H J L Λ).counit := by
  rw [moduleValuedInverseImageCompIso_eq_unique]
  simpa only [Adjunction.ofNatIsoRight_counit, Iso.symm_inv] using
    Adjunction.leftAdjointUniq_hom_counit
      ((moduleValuedInverseImageAdjunction H J L Λ).ofNatIsoRight
        (Functor.sheafPushforwardContinuousComp' e (ModuleCat.{w} Λ) J K L).symm)
      ((moduleValuedInverseImageAdjunction F J K Λ).comp
        (moduleValuedInverseImageAdjunction G K L Λ))

end Composition

end ModuleCat.Sheaf.ConstantRing
