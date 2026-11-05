/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Additive
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Pullback
public import Aglib.Algebra.Homology.RightDerived.Postcomp
public import Aglib.Algebra.Homology.RightDerived.Precomp
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Original native and module-valued higher direct images

The inverse constant-ring equivalence commutes with the actual native
natural-degree higher direct image. The comparison is exact postcomposition,
the original underived direct-image comparison, and exact precomposition by
that same coefficient equivalence. Its maps are module-valued sheaf maps for
the original coefficient actions. No scalar structure is installed on the
native ringed module-sheaf category, and no derived-category model is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.Sheaf.ConstantRing

universe u₁ v₁ u₂ v₂ r w

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (Λ : Type r) [Ring Λ] [F.IsContinuous J K]
  [HasWeakSheafify J RingCat.{r}] [HasWeakSheafify K RingCat.{r}]
  [J.WEqualsLocallyBijective RingCat.{r}] [K.WEqualsLocallyBijective RingCat.{r}]
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [HasSheafify J (ModuleCat.{w} Λ)] [HasSheafify K (ModuleCat.{w} Λ)]

local instance nativeDirectImage_additive :
    (moduleDirectImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ).Additive where
  map_add := by intros; ext U x; rfl

local instance valuedDirectImage_additive :
    (moduleValuedDirectImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ).Additive where
  map_add := by intros; apply ObjectProperty.hom_ext; ext U x; rfl

variable [EnoughInjectives (ModuleSheaf.{u₂, v₂, r, w} K Λ)]

local instance valuedSheaf_enoughInjectives :
    EnoughInjectives (ModuleValuedSheaf.{u₂, v₂, r, w} K Λ) :=
  EnoughInjectives.of_equivalence (moduleSheafEquivalence.{u₂, v₂, r, w} K Λ).functor

/-- The actual higher direct-image comparison through the original coefficient equivalences. -/
def moduleDirectImageRightDerivedComparison (q : ℕ) :
    (moduleDirectImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ).rightDerived q ⋙
        (moduleSheafEquivalence.{u₁, v₁, r, w} J Λ).inverse ≅
      (moduleSheafEquivalence.{u₂, v₂, r, w} K Λ).inverse ⋙
        (moduleValuedDirectImage.{u₁, v₁, u₂, v₂, r, w} F J K Λ).rightDerived q :=
  (Functor.rightDerivedPostcompIso (moduleDirectImage F J K Λ)
    (moduleSheafEquivalence J Λ).inverse q).symm ≪≫
    Functor.rightDerivedNatIsoOfAdditive (moduleDirectImageComparison F J K Λ) q ≪≫
    Functor.rightDerivedPrecompIso (moduleSheafEquivalence K Λ).inverse
      (moduleValuedDirectImage F J K Λ) q

/-- Every original native coefficient morphism preserves the actual higher-image comparison. -/
@[reassoc]
theorem moduleDirectImageRightDerivedComparison_hom_naturality (q : ℕ)
    {M N : ModuleSheaf.{u₂, v₂, r, w} K Λ} (φ : M ⟶ N) :
    (moduleSheafEquivalence J Λ).inverse.map
        (((moduleDirectImage F J K Λ).rightDerived q).map φ) ≫
        (moduleDirectImageRightDerivedComparison F J K Λ q).hom.app N =
      (moduleDirectImageRightDerivedComparison F J K Λ q).hom.app M ≫
        ((moduleValuedDirectImage F J K Λ).rightDerived q).map
          ((moduleSheafEquivalence K Λ).inverse.map φ) :=
  (moduleDirectImageRightDerivedComparison F J K Λ q).hom.naturality φ

/-- On sections the comparison preserves the original coefficient-ring scalar action. -/
theorem moduleDirectImageRightDerivedComparison_hom_app_smul (q : ℕ)
    (M : ModuleSheaf.{u₂, v₂, r, w} K Λ) (U : Cᵒᵖ) (a : Λ)
    (x : (((moduleSheafEquivalence J Λ).inverse.obj
      (((moduleDirectImage F J K Λ).rightDerived q).obj M)).obj.obj U)) :
    (((moduleDirectImageRightDerivedComparison F J K Λ q).hom.app M).hom.app U)
        (a • x) =
      a • (((moduleDirectImageRightDerivedComparison F J K Λ q).hom.app M).hom.app U) x :=
  (((moduleDirectImageRightDerivedComparison F J K Λ q).hom.app M).hom.app U).hom.map_smul a x

end ModuleCat.Sheaf.ConstantRing
