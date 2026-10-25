/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.DirectImage
public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Cohomology
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves

/-! # Genuine constant-module images for proper base-change reduction

The module images are the native site pullback and pushforward with genuine
ZMod-valued sheaves as coefficients. Exactness of the native module inverse
image gives preservation of injectives by the genuine module direct image.
The displayed underlying comparison is the original abelian direct image.
No claim about injectivity after scalar forgetting is made.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

universe u

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard

/-- The actual standard-value category of genuine ZMod-valued etale sheaves. -/
abbrev ZModSheaf (X : Scheme.{u}) (n : ℕ) :=
  Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))

/-- The original underlying abelian sheaf functor of genuine module coefficients. -/
abbrev zmodUnderlying (X : Scheme.{u}) (n : ℕ) :
    ZModSheaf X n ⥤ AbelianSheaf.{u, u + 1} X :=
  sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})

/-- The native site direct image with genuine ZMod-module coefficients. -/
abbrev zmodDirectImage {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) :
    ZModSheaf X n ⥤ ZModSheaf S n :=
  (siteBaseChange f).sheafPushforwardContinuous (ModuleCat.{u + 1} (ZMod n))
    S.smallEtaleTopology X.smallEtaleTopology

/-- The native site inverse image with genuine ZMod-module coefficients. -/
abbrev zmodInverseImage {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) :
    ZModSheaf S n ⥤ ZModSheaf X n :=
  (siteBaseChange f).sheafPullback (ModuleCat.{u + 1} (ZMod n))
    S.smallEtaleTopology X.smallEtaleTopology

/-- The actual native module inverse-image/direct-image adjunction. -/
def zmodImageAdjunction {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) :
    zmodInverseImage f n ⊣ zmodDirectImage f n :=
  (siteBaseChange f).sheafAdjunctionContinuous (ModuleCat.{u + 1} (ZMod n))
    S.smallEtaleTopology X.smallEtaleTopology

/-- Flat presheaf inverse image is exact also for genuine module coefficients;
its comparison with the original abelian Kan extension is the native one. -/
theorem zmodPresheafLan_preservesFiniteLimits {X S : Scheme.{u}}
    (f : X ⟶ S) (n : ℕ) :
    PreservesFiniteLimits
      ((siteBaseChange f).op.lan :
        (S.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ZMod n)) ⥤
          X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ZMod n)) := by
  let G : S.Etale ⥤ X.Etale := siteBaseChange f
  let V : ModuleCat.{u + 1} (ZMod n) ⥤ AddCommGrpCat.{u + 1} :=
    forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1}
  let W₁ : (S.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ZMod n)) ⥤
      S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    (Functor.whiskeringRight S.Etaleᵒᵖ
      (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1}).obj V
  let W₂ : (X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ZMod n)) ⥤
      X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    (Functor.whiskeringRight X.Etaleᵒᵖ
      (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1}).obj V
  have : RepresentablyFlat G := flat_of_preservesFiniteLimits G
  have : PreservesFiniteLimits
      (G.op.lan : (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
        X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
    Functor.LargePresheaf.lan_preservesFiniteLimits.{u + 1, u} G
  let e :
      (G.op.lan : (S.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ZMod n)) ⥤
        X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ZMod n)) ⋙ W₂ ≅
      W₁ ⋙
        (G.op.lan : (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
          X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
    V.lanCompIsoOfPreserves G.op
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u + 1}
  intro J _ _
  have : HasLimitsOfShape J (ModuleCat.{u + 1} (ZMod n)) :=
    ModuleCat.hasLimitsOfShape.{u + 1, u + 1, u + 1, 0}
  have : PreservesLimitsOfSize.{u + 1, u + 1} V :=
    ModuleCat.forget₂AddCommGroup_preservesLimitsOfSize.{u + 1, u + 1, u + 1, 0}
  have : PreservesLimitsOfShape J W₁ :=
    whiskeringRight_preservesLimitsOfShape (C := S.Etaleᵒᵖ)
      (D := ModuleCat.{u + 1} (ZMod n)) (E := AddCommGrpCat.{u + 1}) (J := J) V
  have : PreservesLimitsOfShape J W₂ :=
    whiskeringRight_preservesLimitsOfShape (C := X.Etaleᵒᵖ)
      (D := ModuleCat.{u + 1} (ZMod n)) (E := AddCommGrpCat.{u + 1}) (J := J) V
  have : ReflectsLimitsOfShape J W₂ := reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : PreservesLimitsOfShape J
      ((G.op.lan : (S.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ZMod n)) ⥤
        X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ZMod n)) ⋙ W₂) :=
    preservesLimitsOfShape_of_natIso e.symm
  exact preservesLimitsOfShape_of_reflects_of_preserves _ W₂

/-- The actual inverse image of genuine ZMod coefficients preserves finite limits. -/
instance zmodInverseImage_preservesFiniteLimits {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) :
    PreservesFiniteLimits (zmodInverseImage f n) := by
  have := zmodPresheafLan_preservesFiniteLimits f n
  have := flat_of_preservesFiniteLimits (siteBaseChange f)
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits
    (siteBaseChange f) (ModuleCat.{u + 1} (ZMod n))
    S.smallEtaleTopology X.smallEtaleTopology

/-- The genuine module direct image preserves genuine module injectives,
using exact inverse image and the original native adjunction. -/
theorem zmodDirectImage_preservesInjectiveObjects {X S : Scheme.{u}}
    (f : X ⟶ S) (n : ℕ) :
    (zmodDirectImage f n).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (zmodImageAdjunction f n)

/-- Every additive map between genuine ZMod modules is canonically linear. -/
theorem zmodForget_full (n : ℕ) :
    (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1}).Full where
  map_surjective {X Y} f := by
    let h : X →+ Y := f.hom
    exact ⟨ModuleCat.ofHom (h.toZModLinearMap n), rfl⟩

/-- Forgetting genuine ZMod scalars on the actual etale site is full. -/
theorem zmodUnderlying_full (X : Scheme.{u}) (n : ℕ) : (zmodUnderlying X n).Full := by
  have := zmodForget_full.{u} n
  infer_instance

/-- The genuine module direct image has exactly the original underlying
abelian direct image, with identical pointwise restriction and coefficient maps. -/
def zmodDirectImageUnderlyingIso {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) :
    zmodDirectImage f n ⋙ zmodUnderlying S n ≅
      zmodUnderlying X n ⋙ directImage f :=
  Iso.refl _

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction
