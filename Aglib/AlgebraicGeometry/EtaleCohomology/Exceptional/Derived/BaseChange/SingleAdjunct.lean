/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.SingleAdjunct
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ModuleUnitSquare
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChange

/-! The original module exchange on original unit adjuncts. -/

open CategoryTheory

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wS wX wS' wX'

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

section Ring

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S' Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]

local notation "L₁" => moduleInverseImage f Λ
local notation "L₂" => moduleInverseImage f' Λ
local notation "G" => moduleInverseImage g Λ
local notation "H" => moduleInverseImage g' Λ

/-- The original module exchange on original single adjuncts retains the
given underived normalization. -/
abbrev moduleDerivedBaseChangeMap_originalSingleAdjunct
    {I : ModuleSheaf S Λ} {J : ModuleSheaf X Λ}
    {I' : ModuleSheaf S' Λ} {J' : ModuleSheaf X' Λ}
    (e : (L₁).obj I ≅ J) (e' : (L₂).obj I' ≅ J')
    (u : (G).obj I ≅ I') (v : (H).obj J ≅ J')
    (hs : (moduleInverseImageSquareIso Λ f f' g g' h).hom.app I ≫
      (H).map e.hom ≫ v.hom = (L₂).map u.hom ≫ e'.hom) :=
  let adj₁ := moduleInverseImageAdjunction f Λ
  let adj₂ := moduleInverseImageAdjunction f' Λ
  let α := (moduleInverseImageSquareIso Λ f f' g g' h).hom
  let αD := (moduleDerivedInverseImageSquareIso Λ f f' g g' h).hom
  let s := TwoSquare.mk _ _ _ _ α
  let sD := TwoSquare.mk _ _ _ _ αD
  let β := moduleDerivedBaseChangeMap Λ f f' g g' h
  let hβ := fun K => actualDerivedUnitEquation_of_mate adj₁ adj₂ s sD
    (mateEquiv adj₁ adj₂ s).natTrans β rfl rfl K (moduleDerivedBaseChangeMap_unit Λ f f' g g' h K)
  derivedUnitAdjunct_of_originalSingleExchange adj₁ adj₂ s β hβ e e' u v hs

end Ring

variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f) (n : ℕ)
  [HasDerivedCategory.{wS} (ModuleSheaf S (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wS'} (ModuleSheaf S' (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' (ULift.{u + 1} (ZMod n)))]

/-- The original finite-level exchange preserves the original constant unit adjunct. -/
abbrev moduleDerivedBaseChangeMap_constantUnitAdjunct :=
  moduleDerivedBaseChangeMap_originalSingleAdjunct (ULift.{u + 1} (ZMod n)) f f' g g' h
    (moduleUnitInverseImageIso f n) (moduleUnitInverseImageIso f' n)
    (moduleUnitInverseImageIso g n) (moduleUnitInverseImageIso g' n)
    (moduleUnitInverseImageIso_square_reflected f f' g g' h n)

end AlgebraicGeometry.Scheme.EtaleCohomology
