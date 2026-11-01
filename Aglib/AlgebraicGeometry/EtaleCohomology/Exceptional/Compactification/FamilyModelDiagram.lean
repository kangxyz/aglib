/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.FamilyModelComparison
public import Aglib.CategoryTheory.Filtered.InvertibleDiagramNaturality

/-! # Original compactification diagrams under independent model-family change -/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM₀ wM₁
variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ))
  (models₀ : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM₀} (ModuleSheaf C.Xbar Λ))
  (models₁ : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM₁} (ModuleSheaf C.Xbar Λ))

/-- An explicit-model form of the original compactification diagram. -/
abbrev moduleCompactificationDiagramModel
    (models : ∀ C : Hom.DenseCompactification f,
      HasDerivedCategory.{wM₀} (ModuleSheaf C.Xbar Λ)) :=
  @moduleCompactificationDiagram X S f _ Λ _ hX hS models

/-- Every arrow of the explicitly modelled diagram is its original invertible transition. -/
instance moduleCompactificationDiagramModel_map_isIso
    (C D : (Hom.DenseCompactification f)ᵒᵖ) (a : C ⟶ D) :
    IsIso ((moduleCompactificationDiagramModel f Λ hX hS models₀).map a) :=
  @moduleCompactificationDiagram_map_isIso X S f _ Λ _ hX hS models₀ C D a

/-- The same-family mixed identity transition is the original identity. -/
theorem moduleCompactificationFamilyComparison_self (C : Hom.DenseCompactification f) :
    moduleCompactificationFamilyComparison f Λ hX hS models₀ models₀ C = Iso.refl _ := by
  apply Iso.ext
  exact @moduleCompactificationTransition_id X S f _ Λ _ hX hS models₀ C

/-- The original mixed identity transitions form an actual isomorphism of diagrams. -/
def moduleCompactificationFamilyDiagramIso :
    moduleCompactificationDiagramModel f Λ hX hS models₀ ≅
      (𝟭 (Hom.DenseCompactification f)).op ⋙
        moduleCompactificationDiagramModel f Λ hX hS models₁ :=
  NatIso.ofComponents
    (fun C => moduleCompactificationFamilyComparison f Λ hX hS models₀ models₁ C.unop)
    (by
      intro C D a
      exact moduleCompactificationFamilyComparison_naturality f Λ hX hS models₀ models₁ a.unop)

/-- The coherent family comparison commutes with every original canonical comparison. -/
theorem moduleCompactificationFamilyComparison_canonical (C D : Hom.DenseCompactification f) :
    moduleCompactificationFamilyComparison f Λ hX hS models₀ models₁ C ≪≫
        (@moduleCompactificationComparison X S f _ Λ _ hX hS models₁ C D) =
      (@moduleCompactificationComparison X S f _ Λ _ hX hS models₀ C D) ≪≫
        moduleCompactificationFamilyComparison f Λ hX hS models₀ models₁ D :=
  Functor.cofilteredComparison_natIso (𝟭 (Hom.DenseCompactification f))
    (moduleCompactificationFamilyDiagramIso f Λ hX hS models₀ models₁) C D

end AlgebraicGeometry.Scheme.EtaleCohomology
