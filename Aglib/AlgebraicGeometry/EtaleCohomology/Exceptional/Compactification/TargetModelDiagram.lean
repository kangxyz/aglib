/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.TargetModelComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.Independence
public import Aglib.CategoryTheory.Filtered.InvertibleDiagramNaturality

/-! # Canonical target transport of compactification diagrams and their comparisons -/

@[expose] public noncomputable section
open CategoryTheory DerivedCategory.Plus Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS₀ wS₁ wM
variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hS₀ : HasDerivedCategory.{wS₀} (ModuleSheaf S Λ))
  (hS₁ : HasDerivedCategory.{wS₁} (ModuleSheaf S Λ))
  (models : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))

/-- The original diagram postcomposed with the canonical native target equivalence. -/
def moduleCompactificationTargetTransportDiagram :=
  @moduleCompactificationDiagram X S f _ Λ _ hX hS₀ models ⋙
    (Functor.whiskeringRight _ _ _).obj (canonicalEquivalence hS₀ hS₁).functor

instance moduleCompactificationTargetTransportDiagram_map_isIso
    (C D : (Hom.DenseCompactification f)ᵒᵖ) (a : C ⟶ D) :
    IsIso ((moduleCompactificationTargetTransportDiagram f Λ hX hS₀ hS₁ models).map a) := by
  let := @moduleCompactificationDiagram_map_isIso X S f _ Λ _ hX hS₀ models C D a
  change IsIso (Functor.whiskerRight
    ((@moduleCompactificationDiagram X S f _ Λ _ hX hS₀ models).map a) _)
  infer_instance

/-- Target-model comparison is an isomorphism of the original refinement diagrams. -/
def moduleCompactificationTargetDiagramIso :
    moduleCompactificationTargetTransportDiagram f Λ hX hS₀ hS₁ models ≅
      (𝟭 (Hom.DenseCompactification f)).op ⋙
        @moduleCompactificationDiagram X S f _ Λ _ hX hS₁ models :=
  NatIso.ofComponents
    (fun C => moduleCompactificationTargetComparison f Λ hX hS₀ hS₁ models C.unop)
    (by intro C D a
        exact moduleCompactificationTargetComparison_naturality f Λ hX hS₀ hS₁ models a.unop)

/-- Native target transport commutes with every original canonical compactification comparison. -/
theorem moduleCompactificationTargetComparison_canonical (C D : Hom.DenseCompactification f) :
    moduleCompactificationTargetComparison f Λ hX hS₀ hS₁ models C ≪≫
        @moduleCompactificationComparison X S f _ Λ _ hX hS₁ models C D =
      Functor.isoWhiskerRight
        (@moduleCompactificationComparison X S f _ Λ _ hX hS₀ models C D)
          (canonicalEquivalence hS₀ hS₁).functor ≪≫
        moduleCompactificationTargetComparison f Λ hX hS₀ hS₁ models D := by
  let := fun C D a =>
    @moduleCompactificationDiagram_map_isIso X S f _ Λ _ hX hS₀ models C D a
  let := fun C D a =>
    @moduleCompactificationDiagram_map_isIso X S f _ Λ _ hX hS₁ models C D a
  have hn := Functor.cofilteredComparison_natIso (𝟭 (Hom.DenseCompactification f))
    (moduleCompactificationTargetDiagramIso f Λ hX hS₀ hS₁ models) C D
  dsimp only [moduleCompactificationTargetTransportDiagram] at hn
  rw [← Functor.cofilteredComparison_postcomp] at hn
  exact hn

end AlgebraicGeometry.Scheme.EtaleCohomology
