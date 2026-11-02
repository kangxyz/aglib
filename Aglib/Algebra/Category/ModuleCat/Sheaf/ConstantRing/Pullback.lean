/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Images
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-! # Native constant-ring inverse image and whole adjunction transport

The actual module-valued pullback and the actual coefficient equivalences
construct a left adjoint to native ringed pushforward. The ringed inverse
image remains the native pullback. Its comparison is fixed by both whole
unit and counit equations, before any geometric realization is supplied.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.Sheaf.ConstantRing

universe u₁ v₁ u₂ v₂ r w

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (Λ : Type r) [Ring Λ] [F.IsContinuous J K]

section ModuleValued

variable [∀ P : Cᵒᵖ ⥤ ModuleCat.{w} Λ, F.op.HasLeftKanExtension P]
  [HasWeakSheafify K (ModuleCat.{w} Λ)]

/-- The original continuous-site inverse image of module-valued sheaves. -/
abbrev moduleValuedInverseImage :
    ModuleValuedSheaf.{u₁, v₁, r, w} J Λ ⥤ ModuleValuedSheaf.{u₂, v₂, r, w} K Λ :=
  F.sheafPullback (ModuleCat.{w} Λ) J K

/-- The original module-valued continuous-site adjunction. -/
abbrev moduleValuedInverseImageAdjunction :
    moduleValuedInverseImage F J K Λ ⊣ moduleValuedDirectImage F J K Λ :=
  F.sheafAdjunctionContinuous (ModuleCat.{w} Λ) J K

end ModuleValued

section Comparison

variable [HasWeakSheafify J RingCat.{r}] [HasWeakSheafify K RingCat.{r}]
  [J.WEqualsLocallyBijective RingCat.{r}] [K.WEqualsLocallyBijective RingCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- The direct-image comparison on each original section module is restriction of scalars. -/
def moduleDirectImageComparisonComponent (M : ModuleSheaf.{u₂, v₂, r, w} K Λ) (U : Cᵒᵖ) :
    (((moduleSheafEquivalence J Λ).inverse.obj
      ((moduleDirectImage F J K Λ).obj M)).obj.obj U) ≅
    (((moduleValuedDirectImage F J K Λ).obj
      ((moduleSheafEquivalence K Λ).inverse.obj M)).obj.obj U) :=
  (ModuleCat.restrictScalarsComp'App
    ((constantRingUnit J Λ).app U).hom ((constantRingMap F J K Λ).hom.app U).hom
    ((constantRingUnit K Λ).app (F.op.obj U)).hom
    (congrArg RingCat.Hom.hom (constantRingUnit_comp_constantRingMap_app F J K Λ U).symm)
    (ModuleCat.of ((constantRing K Λ).obj.obj (F.op.obj U))
      (M.val.obj (F.op.obj U)))).symm

/-- The actual equivalence comparison for genuine native ringed direct image. -/
def moduleDirectImageComparison :
    moduleDirectImage F J K Λ ⋙ (moduleSheafEquivalence J Λ).inverse ≅
      (moduleSheafEquivalence K Λ).inverse ⋙ moduleValuedDirectImage F J K Λ :=
  NatIso.ofComponents (fun M => ObjectProperty.isoMk _
    (NatIso.ofComponents (moduleDirectImageComparisonComponent F J K Λ M)
      (by intros; ext x; rfl)))
    (by intros; apply ObjectProperty.hom_ext; ext U x; rfl)

/-- Direct image agrees with the original equivalence-transported module-valued functor. -/
def moduleDirectImageTransportIso : moduleDirectImage F J K Λ ≅
    (moduleSheafEquivalence K Λ).inverse ⋙ moduleValuedDirectImage F J K Λ ⋙
      (moduleSheafEquivalence J Λ).functor :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (moduleSheafEquivalence J Λ).counitIso.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleDirectImageComparison F J K Λ)
      (moduleSheafEquivalence J Λ).functor ≪≫
    Functor.associator _ _ _

section Adjunction

variable [∀ P : Cᵒᵖ ⥤ ModuleCat.{w} Λ, F.op.HasLeftKanExtension P]
  [HasWeakSheafify K (ModuleCat.{w} Λ)]

/-- The original coefficient equivalences transport the actual site adjunction. -/
def moduleTransportAdjunction :
    ((moduleSheafEquivalence J Λ).inverse ⋙ moduleValuedInverseImage F J K Λ) ⋙
      (moduleSheafEquivalence K Λ).functor ⊣ moduleDirectImage F J K Λ :=
  (((moduleSheafEquivalence J Λ).symm.toAdjunction.comp
    (moduleValuedInverseImageAdjunction F J K Λ)).comp
      (moduleSheafEquivalence K Λ).toAdjunction).ofNatIsoRight
        (moduleDirectImageTransportIso F J K Λ).symm

/-- The genuine ringed pushforward has a left adjoint supplied by the original site construction. -/
instance moduleDirectImage_isRightAdjoint :
    (moduleDirectImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ).IsRightAdjoint :=
  (moduleTransportAdjunction F J K Λ).isRightAdjoint

/-- The same proved witness at the literal native pushforward type. -/
local instance nativePushforward_isRightAdjoint :
    (SheafOfModules.pushforward.{w} (constantRingMap F J K Λ)).IsRightAdjoint :=
  moduleDirectImage_isRightAdjoint F J K Λ

/-- Genuine native pullback along the original constant-ring morphism. -/
def moduleInverseImage :
    ModuleSheaf.{u₁, v₁, r, w} J Λ ⥤ ModuleSheaf.{u₂, v₂, r, w} K Λ := by
  let : (SheafOfModules.pushforward.{w} (constantRingMap F J K Λ)).IsRightAdjoint :=
    moduleDirectImage_isRightAdjoint F J K Λ
  exact SheafOfModules.pullback.{w} (constantRingMap F J K Λ)

/-- The actual native ringed pullback/direct-image adjunction. -/
def moduleInverseImageAdjunction : moduleInverseImage F J K Λ ⊣ moduleDirectImage F J K Λ := by
  let : (SheafOfModules.pushforward.{w} (constantRingMap F J K Λ)).IsRightAdjoint :=
    moduleDirectImage_isRightAdjoint F J K Λ
  exact SheafOfModules.pullbackPushforwardAdjunction.{w} (constantRingMap F J K Λ)

/-- Native inverse image retains its original ringed pullback value. -/
theorem moduleInverseImage_eq_original :
    moduleInverseImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ =
      SheafOfModules.pullback.{w} (constantRingMap F J K Λ) := rfl

/-- Native pullback agrees with the actual equivalence-transported site pullback. -/
def moduleInverseImageTransportIso : moduleInverseImage F J K Λ ≅
    ((moduleSheafEquivalence J Λ).inverse ⋙ moduleValuedInverseImage F J K Λ) ⋙
      (moduleSheafEquivalence K Λ).functor :=
  (moduleInverseImageAdjunction F J K Λ).leftAdjointUniq (moduleTransportAdjunction F J K Λ)

/-- The WHOLE comparison preserves the original native adjunction unit. -/
theorem moduleInverseImageTransportIso_unit :
    (moduleInverseImageAdjunction F J K Λ).unit ≫
        Functor.whiskerRight (moduleInverseImageTransportIso F J K Λ).hom
          (moduleDirectImage F J K Λ) =
      (moduleTransportAdjunction F J K Λ).unit :=
  Adjunction.unit_leftAdjointUniq_hom _ _

/-- The component of the whole original-unit comparison. -/
@[reassoc]
theorem moduleInverseImageTransportIso_unit_app (M : ModuleSheaf.{u₁, v₁, r, w} J Λ) :
    (moduleInverseImageAdjunction F J K Λ).unit.app M ≫
      (moduleDirectImage F J K Λ).map
        ((moduleInverseImageTransportIso F J K Λ).hom.app M) =
      (moduleTransportAdjunction F J K Λ).unit.app M := by
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app] using
    NatTrans.congr_app (moduleInverseImageTransportIso_unit F J K Λ) M

/-- The WHOLE comparison preserves the original native adjunction counit. -/
theorem moduleInverseImageTransportIso_counit :
    Functor.whiskerLeft (moduleDirectImage F J K Λ)
        (moduleInverseImageTransportIso F J K Λ).hom ≫
      (moduleTransportAdjunction F J K Λ).counit =
        (moduleInverseImageAdjunction F J K Λ).counit :=
  Adjunction.leftAdjointUniq_hom_counit _ _

/-- The component of the whole original-counit comparison. -/
@[reassoc]
theorem moduleInverseImageTransportIso_counit_app (M : ModuleSheaf.{u₂, v₂, r, w} K Λ) :
    (moduleInverseImageTransportIso F J K Λ).hom.app
        ((moduleDirectImage F J K Λ).obj M) ≫
      (moduleTransportAdjunction F J K Λ).counit.app M =
        (moduleInverseImageAdjunction F J K Λ).counit.app M := by
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app] using
    NatTrans.congr_app (moduleInverseImageTransportIso_counit F J K Λ) M

end Adjunction

end Comparison

end ModuleCat.Sheaf.ConstantRing
