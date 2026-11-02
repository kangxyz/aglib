/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceIsoNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.MixedModelTransition
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompactificationIndependence
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
    @moduleUnboundedCompactificationMixedTransition X S f _ Λ _ hX hS C D a hC₀ hD₀ ≫
        @moduleUnboundedCompactificationMixedTransition X S f _ Λ _ hX hS C C (𝟙 C) hC₁ hC₀ =
      @moduleUnboundedCompactificationMixedTransition X S f _ Λ _ hX hS D D (𝟙 D) hD₁ hD₀ ≫
        @moduleUnboundedCompactificationMixedTransition X S f _ Λ _ hX hS C D a hC₁ hD₁ := by
  have h₀ := @moduleUnboundedCompactificationMixedTransition_comp X S f _ Λ _ hX hS C C
    (𝟙 C) hC₁ hC₀ D a hD₀
  have h₁ := @moduleUnboundedCompactificationMixedTransition_comp X S f _ Λ _ hX hS C D
    a hC₁ hD₁ D (𝟙 D) hD₀
  simpa only [Category.id_comp, Category.comp_id] using h₀.symm.trans h₁

variable {X X' S : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S)
  [QuasiCompact f] [QuasiCompact f'] (e : X' ≅ X) (he : e.hom ≫ f = f')
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hX' : HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- Original raw source transport followed by the actual mixed identity refinement. -/
def moduleUnboundedCompactificationSourceIsoModel (C : Hom.DenseCompactification f)
    [sourceModel : HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
    [targetModel : HasDerivedCategory.{wN}
      (ModuleSheaf ((Hom.DenseCompactification.sourceIso f' e he).obj C).Xbar Λ)] :
    (letI : HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ) := sourceModel
     moduleUnboundedCompactificationFunctor f Λ C) ≅
    (letI : HasDerivedCategory.{wN}
        (ModuleSheaf ((Hom.DenseCompactification.sourceIso f' e he).obj C).Xbar Λ) := targetModel
     moduleUnboundedDerivedInverseImage Λ e.hom ⋙
       moduleUnboundedCompactificationFunctor f' Λ
         ((Hom.DenseCompactification.sourceIso f' e he).obj C)) := by
  let D := (Hom.DenseCompactification.sourceIso f' e he).obj C
  let hOld : HasDerivedCategory.{wM} (ModuleSheaf D.Xbar Λ) := sourceModel
  letI := @moduleUnboundedCompactificationMixedTransition_isIso X' S f' _ Λ _ hX' hS D D
    (𝟙 D) targetModel hOld N hN hΛ
  let m := asIso (@moduleUnboundedCompactificationMixedTransition X' S f' _ Λ _ hX' hS D D
    (𝟙 D) targetModel hOld)
  letI : HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ) := sourceModel
  exact moduleUnboundedRawCompactificationSourceIso e Λ f' he C.toCompactification ≪≫
    Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ e.hom) m

variable
  [sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [targetModels : ∀ D : Hom.DenseCompactification f',
    HasDerivedCategory.{wN} (ModuleSheaf D.Xbar Λ)]


/-- Source transport is natural for the actual refinement arrows and independent target models. -/
theorem moduleUnboundedCompactificationSourceIsoModel_naturality
    {C D : Hom.DenseCompactification f} (a : C ⟶ D) :
    moduleUnboundedCompactificationTransition Λ a ≫
        (moduleUnboundedCompactificationSourceIsoModel f f' e he Λ N hN hΛ C
          (sourceModel := sourceModels C)
          (targetModel := targetModels ((Hom.DenseCompactification.sourceIso f' e he).obj C))).hom =
      (moduleUnboundedCompactificationSourceIsoModel f f' e he Λ N hN hΛ D
          (sourceModel := sourceModels D)
          (targetModel := targetModels ((Hom.DenseCompactification.sourceIso f' e he).obj D))).hom ≫
        Functor.whiskerLeft (moduleUnboundedDerivedInverseImage Λ e.hom)
          (moduleUnboundedCompactificationTransition Λ
            ((Hom.DenseCompactification.sourceIso f' e he).map a)) := by
  let C' := (Hom.DenseCompactification.sourceIso f' e he).obj C
  let D' := (Hom.DenseCompactification.sourceIso f' e he).obj D
  let a' := (Hom.DenseCompactification.sourceIso f' e he).map a
  let hC : HasDerivedCategory.{wM} (ModuleSheaf C'.Xbar Λ) := sourceModels C
  let hD : HasDerivedCategory.{wM} (ModuleSheaf D'.Xbar Λ) := sourceModels D
  let : HasDerivedCategory.{wN} (ModuleSheaf C'.Xbar Λ) := targetModels C'
  let : HasDerivedCategory.{wN} (ModuleSheaf D'.Xbar Λ) := targetModels D'
  let : HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ) := sourceModels C
  let : HasDerivedCategory.{wM} (ModuleSheaf D.Xbar Λ) := sourceModels D
  exact sourceIsoComponent_naturality (moduleUnboundedDerivedInverseImage Λ e.hom)
    (moduleUnboundedCompactificationTransition Λ a)
    (@moduleUnboundedCompactificationMixedTransition X' S f' _ Λ _ hX' hS C' D' a' hC hD)
    (moduleUnboundedCompactificationTransition Λ a')
    (moduleUnboundedRawCompactificationSourceIso e Λ f' he D.toCompactification)
    (moduleUnboundedRawCompactificationSourceIso e Λ f' he C.toCompactification)
    (@asIso _ _ _ _
      (@moduleUnboundedCompactificationMixedTransition X' S f' _ Λ _ hX' hS D' D' (𝟙 D')
        (targetModels D') hD)
      (@moduleUnboundedCompactificationMixedTransition_isIso X' S f' _ Λ _ hX' hS D' D' (𝟙 D')
        (targetModels D') hD N hN hΛ))
    (@asIso _ _ _ _
      (@moduleUnboundedCompactificationMixedTransition X' S f' _ Λ _ hX' hS C' C' (𝟙 C')
        (targetModels C') hC)
      (@moduleUnboundedCompactificationMixedTransition_isIso X' S f' _ Λ _ hX' hS C' C' (𝟙 C')
        (targetModels C') hC N hN hΛ))
    (moduleUnboundedCompactifiedSourceIso_refinement_naturality e C.j D.j a.hom
      (Hom.DenseCompactification.isPullback_open a)
      (Hom.DenseCompactification.isPullback_open a') C.p D.p a.base_fac Λ)
    (mixedIdentity_naturality Λ hX' hS a' hC (targetModels C') hD (targetModels D'))

/-- The target diagram is preceded by the actual native source inverse image. -/
def moduleUnboundedCompactificationSourceIsoTargetDiagram :
    (Hom.DenseCompactification f')ᵒᵖ ⥤
      (DerivedCategory (ModuleSheaf X Λ) ⥤
        DerivedCategory (ModuleSheaf S Λ)) :=
  moduleUnboundedCompactificationDiagram (f := f') Λ ⋙
    (Functor.whiskeringLeft _ _ _).obj (moduleUnboundedDerivedInverseImage Λ e.hom)

/-- Actual source transport, including independent-model comparisons, is a diagram isomorphism. -/
def moduleUnboundedCompactificationSourceIsoDiagram :
    moduleUnboundedCompactificationDiagram (f := f) Λ ≅
      (Hom.DenseCompactification.sourceIso f' e he).op ⋙
        moduleUnboundedCompactificationSourceIsoTargetDiagram f' e Λ :=
  NatIso.ofComponents
    (fun C => moduleUnboundedCompactificationSourceIsoModel f f' e he Λ N hN hΛ C.unop
      (sourceModel := sourceModels C.unop)
      (targetModel := targetModels ((Hom.DenseCompactification.sourceIso f' e he).obj C.unop)))
    (by
      intro C D a
      exact moduleUnboundedCompactificationSourceIsoModel_naturality f f' e he Λ N hN hΛ a.unop)

end AlgebraicGeometry.Scheme.EtaleCohomology
