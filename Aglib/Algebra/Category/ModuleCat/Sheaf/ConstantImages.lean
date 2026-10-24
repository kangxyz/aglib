/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantCoefficients
public import Aglib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves

/-! # Native images of constant-ring module sheaves

The native sheaf pullback commutes with original scalar forgetting. Its
comparison uses the native left Kan extension and sheafification maps, rather
than replacing either coefficient functor. For a representably flat continuous
site functor the genuine module pullback is exact.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.Sheaf

universe u v r w

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (R : Type r) [Ring R] (G : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K]

attribute [local instance] hasSheafify forget_preservesSheafification

local instance constantImagesPreservesColimits : PreservesColimitsOfSize.{w, w}
    (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) :=
  ModuleCat.forget₂PreservesColimitsOfSize.{w, r, w, w} R

/-- Native module direct image has precisely the original abelian direct
image, including the same section restriction and coefficient maps. -/
def pushforwardUnderlyingIso :
    G.sheafPushforwardContinuous (ModuleCat.{max u v} R) J K ⋙ underlying R J ≅
      underlying R K ⋙ G.sheafPushforwardContinuous AddCommGrpCat.{max u v} J K :=
  Iso.refl _

/-- The native inverse-image comparison with original abelian coefficients. -/
def pullbackUnderlyingIso :
    G.sheafPullback (ModuleCat.{max u v} R) J K ⋙ underlying R K ≅
      underlying R J ⋙ G.sheafPullback AddCommGrpCat.{max u v} J K := by
  let eM := Functor.sheafPullbackConstruction.sheafPullbackIso G
    (ModuleCat.{max u v} R) J K
  let eA := Functor.sheafPullbackConstruction.sheafPullbackIso G
    AddCommGrpCat.{max u v} J K
  let c := sheafComposeNatIso K
    (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
    (sheafificationAdjunction K (ModuleCat.{max u v} R))
    (sheafificationAdjunction K AddCommGrpCat.{max u v})
  let k := (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).lanCompIsoOfPreserves G.op
  exact Functor.isoWhiskerRight eM (underlying R K) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J (ModuleCat.{max u v} R) ⋙ G.op.lan) c.symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (sheafToPresheaf J (ModuleCat.{max u v} R)) k)
      (presheafToSheaf K AddCommGrpCat.{max u v}) ≪≫
    Functor.isoWhiskerLeft (underlying R J) eA.symm

/-- Every original module coefficient map commutes with the actual comparison. -/
@[reassoc]
theorem pullbackUnderlyingIso_naturality
    {F F' : Sheaf J (ModuleCat.{max u v} R)} (f : F ⟶ F') :
    (underlying R K).map ((G.sheafPullback (ModuleCat.{max u v} R) J K).map f) ≫
        (pullbackUnderlyingIso R G J K).hom.app F' =
      (pullbackUnderlyingIso R G J K).hom.app F ≫
        (G.sheafPullback AddCommGrpCat.{max u v} J K).map ((underlying R J).map f) :=
  (pullbackUnderlyingIso R G J K).hom.naturality f

/-- Flat left Kan extension of genuine module presheaves preserves finite
limits, by the original additive comparison and reflection of limits. -/
theorem presheafLan_preservesFiniteLimits [RepresentablyFlat G] :
    PreservesFiniteLimits
      (G.op.lan : (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ⥤ Dᵒᵖ ⥤ ModuleCat.{max u v} R) := by
  let V := forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}
  let W₁ := (Functor.whiskeringRight Cᵒᵖ
    (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).obj V
  let W₂ := (Functor.whiskeringRight Dᵒᵖ
    (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).obj V
  have : PreservesFiniteLimits
      (G.op.lan : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ Dᵒᵖ ⥤ AddCommGrpCat.{max u v}) :=
    Functor.LargePresheaf.lan_preservesFiniteLimits G
  let e :
      (G.op.lan : (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ⥤ Dᵒᵖ ⥤ ModuleCat.{max u v} R) ⋙ W₂ ≅
        W₁ ⋙ (G.op.lan :
          (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ Dᵒᵖ ⥤ AddCommGrpCat.{max u v}) :=
    V.lanCompIsoOfPreserves G.op
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{max u v}
  intro I _ _
  have : HasLimitsOfShape I (ModuleCat.{max u v} R) :=
    ModuleCat.hasLimitsOfShape.{max u v, max u v, max u v, r}
  have : PreservesLimitsOfSize.{max u v, max u v} V :=
    ModuleCat.forget₂AddCommGroup_preservesLimitsOfSize.{max u v, max u v, max u v, r}
  have : PreservesLimitsOfShape I W₁ :=
    whiskeringRight_preservesLimitsOfShape (C := Cᵒᵖ)
      (D := ModuleCat.{max u v} R) (E := AddCommGrpCat.{max u v}) (J := I) V
  have : PreservesLimitsOfShape I W₂ :=
    whiskeringRight_preservesLimitsOfShape (C := Dᵒᵖ)
      (D := ModuleCat.{max u v} R) (E := AddCommGrpCat.{max u v}) (J := I) V
  have : ReflectsLimitsOfShape I W₂ := reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : PreservesLimitsOfShape I
      ((G.op.lan : (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ⥤ Dᵒᵖ ⥤ ModuleCat.{max u v} R) ⋙ W₂) :=
    preservesLimitsOfShape_of_natIso e.symm
  exact preservesLimitsOfShape_of_reflects_of_preserves _ W₂

/-- Native pullback of constant-ring modules is left exact on a flat site map. -/
theorem pullback_preservesFiniteLimits [RepresentablyFlat G] :
    PreservesFiniteLimits (G.sheafPullback (ModuleCat.{max u v} R) J K) := by
  have := presheafLan_preservesFiniteLimits R G
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits G
    (ModuleCat.{max u v} R) J K

end ModuleCat.Sheaf
