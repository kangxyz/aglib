/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.NormalizedExchangeNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawSourceIsoNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ModelComparisonCoherence
public import Aglib.CategoryTheory.Filtered.InvertibleDiagramNaturality

/-!
# Actual source transport with independent target compactification models

The original source comparison is followed by the original mixed-model identity
refinement. The independently supplied target family is never identified with
the inherited ambient model of a transported source compactification.
-/

@[expose] public noncomputable section
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wX' wS wM wN wC₀ wC₁ wD₀ wD₁

private theorem mixedIdentity_naturality
    {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
    (Λ : Type (u + 1)) [Ring Λ]
    (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
    (hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ))
    {C D : Hom.DenseCompactification f} (a : C ⟶ D)
    (hC₀ : HasDerivedCategory.{wC₀} (ModuleSheaf C.Xbar Λ))
    (hC₁ : HasDerivedCategory.{wC₁} (ModuleSheaf C.Xbar Λ))
    (hD₀ : HasDerivedCategory.{wD₀} (ModuleSheaf D.Xbar Λ))
    (hD₁ : HasDerivedCategory.{wD₁} (ModuleSheaf D.Xbar Λ)) :
    @moduleCompactificationMixedTransition X S f _ Λ _ hX hS C D a hC₀ hD₀ ≫
        @moduleCompactificationMixedTransition X S f _ Λ _ hX hS C C (𝟙 C) hC₁ hC₀ =
      @moduleCompactificationMixedTransition X S f _ Λ _ hX hS D D (𝟙 D) hD₁ hD₀ ≫
        @moduleCompactificationMixedTransition X S f _ Λ _ hX hS C D a hC₁ hD₁ := by
  have h₀ := @moduleCompactificationMixedTransition_comp X S f _ Λ _ hX hS C C
    (𝟙 C) hC₁ hC₀ D a hD₀
  have h₁ := @moduleCompactificationMixedTransition_comp X S f _ Λ _ hX hS C D
    a hC₁ hD₁ D (𝟙 D) hD₀
  simpa only [Category.id_comp, Category.comp_id] using h₀.symm.trans h₁

variable {X X' S : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S)
  [QuasiCompact f] [QuasiCompact f'] (e : X' ≅ X) (he : e.hom ≫ f = f')
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hX' : HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [targetModels : ∀ D : Hom.DenseCompactification f',
    HasDerivedCategory.{wN} (ModuleSheaf D.Xbar Λ)]

/-- Original raw source transport followed by the actual mixed identity refinement. -/
def moduleCompactificationSourceIsoModel (C : Hom.DenseCompactification f) :
    moduleCompactificationFunctor f Λ C ≅
      moduleDerivedInverseImageTorsion e.hom Λ ⋙
        moduleCompactificationFunctor f' Λ
          ((Hom.DenseCompactification.sourceIso f' e he).obj C) := by
  let D := (Hom.DenseCompactification.sourceIso f' e he).obj C
  let hOld : HasDerivedCategory.{wM} (ModuleSheaf D.Xbar Λ) := sourceModels C
  let m := asIso (@moduleCompactificationMixedTransition X' S f' _ Λ _ hX' hS D D
    (𝟙 D) (targetModels D) hOld)
  letI : HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ) := sourceModels C
  exact moduleRawCompactificationSourceIso e Λ f' he C.toCompactification ≪≫
    Functor.isoWhiskerLeft (moduleDerivedInverseImageTorsion e.hom Λ) m

/-- Source transport is natural for the actual refinement arrows and independent target models. -/
theorem moduleCompactificationSourceIsoModel_naturality
    {C D : Hom.DenseCompactification f} (a : C ⟶ D) :
    moduleCompactificationTransition Λ a ≫
        (moduleCompactificationSourceIsoModel f f' e he Λ C).hom =
      (moduleCompactificationSourceIsoModel f f' e he Λ D).hom ≫
        Functor.whiskerLeft (moduleDerivedInverseImageTorsion e.hom Λ)
          (moduleCompactificationTransition Λ
            ((Hom.DenseCompactification.sourceIso f' e he).map a)) := by
  let C' := (Hom.DenseCompactification.sourceIso f' e he).obj C
  let D' := (Hom.DenseCompactification.sourceIso f' e he).obj D
  let a' := (Hom.DenseCompactification.sourceIso f' e he).map a
  let hC : HasDerivedCategory.{wM} (ModuleSheaf C'.Xbar Λ) := sourceModels C
  let hD : HasDerivedCategory.{wM} (ModuleSheaf D'.Xbar Λ) := sourceModels D
  let : HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ) := sourceModels C
  let : HasDerivedCategory.{wM} (ModuleSheaf D.Xbar Λ) := sourceModels D
  exact sourceIsoComponent_naturality (moduleDerivedInverseImageTorsion e.hom Λ)
    (moduleCompactificationTransition Λ a)
    (@moduleCompactificationMixedTransition X' S f' _ Λ _ hX' hS C' D' a' hC hD)
    (moduleCompactificationTransition Λ a')
    (moduleRawCompactificationSourceIso e Λ f' he D.toCompactification)
    (moduleRawCompactificationSourceIso e Λ f' he C.toCompactification)
    (@asIso _ _ _ _
      (@moduleCompactificationMixedTransition X' S f' _ Λ _ hX' hS D' D' (𝟙 D')
        (targetModels D') hD)
      (@moduleCompactificationMixedTransition_isIso X' S f' _ Λ _ hX' hS D' D' (𝟙 D')
        (targetModels D') hD))
    (@asIso _ _ _ _
      (@moduleCompactificationMixedTransition X' S f' _ Λ _ hX' hS C' C' (𝟙 C')
        (targetModels C') hC)
      (@moduleCompactificationMixedTransition_isIso X' S f' _ Λ _ hX' hS C' C' (𝟙 C')
        (targetModels C') hC))
    (moduleRawCompactificationSourceIso_refinement_naturality e f' he
      C.toCompactification D.toCompactification a.hom
      (Hom.DenseCompactification.isPullback_open a)
      (Hom.DenseCompactification.isPullback_open a') a.base_fac Λ)
    (mixedIdentity_naturality Λ hX' hS a' hC (targetModels C') hD (targetModels D'))

/-- The target diagram is preceded by the actual native source inverse image. -/
def moduleCompactificationSourceIsoTargetDiagram :
    (Hom.DenseCompactification f')ᵒᵖ ⥤
      ((moduleTorsionCohomologyPlus X Λ).FullSubcategory ⥤
        DerivedCategory.Plus (ModuleSheaf S Λ)) :=
  moduleCompactificationDiagram (f := f') Λ ⋙
    (Functor.whiskeringLeft _ _ _).obj (moduleDerivedInverseImageTorsion e.hom Λ)

/-- Actual source transport, including independent-model comparisons, is a diagram isomorphism. -/
def moduleCompactificationSourceIsoDiagram :
    moduleCompactificationDiagram (f := f) Λ ≅
      (Hom.DenseCompactification.sourceIso f' e he).op ⋙
        moduleCompactificationSourceIsoTargetDiagram f' e Λ :=
  NatIso.ofComponents
    (fun C => moduleCompactificationSourceIsoModel f f' e he Λ C.unop)
    (by intro C D a; exact moduleCompactificationSourceIsoModel_naturality f f' e he Λ a.unop)

end AlgebraicGeometry.Scheme.EtaleCohomology
