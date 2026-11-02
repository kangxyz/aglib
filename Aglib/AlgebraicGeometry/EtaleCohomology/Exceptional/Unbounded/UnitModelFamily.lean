/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.UnitModelComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceIsoIdentity
public import Aglib.CategoryTheory.Filtered.InvertibleDiagramNaturality
public import Aglib.CategoryTheory.Functor.IsoSquarePostcompose

/-! # Original unbounded family transport and single-value comparisons -/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM₀ wM₁ wC
variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ))
  (models₀ : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM₀} (ModuleSheaf C.Xbar Λ))
  (models₁ : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM₁} (ModuleSheaf C.Xbar Λ))
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- Original mixed identity maps give the actual diagram transformation. -/
def moduleUnboundedCompactificationFamilyDiagramIso :
    @moduleUnboundedCompactificationDiagram X S f _ Λ _ hX hS models₀ ≅
      (𝟭 (Hom.DenseCompactification f)).op ⋙
        @moduleUnboundedCompactificationDiagram X S f _ Λ _ hX hS models₁ :=
  NatIso.ofComponents
    (fun C => moduleUnboundedCompactificationFamilyComparison f Λ hX hS
      models₀ models₁ N hN hΛ C.unop)
    (by
      intro C D a
      exact @moduleUnboundedCompactificationSingleModelIso_refinement X S f _ Λ _ hX hS
        models₀ N hN hΛ D.unop C.unop a.unop (models₁ D.unop) (models₁ C.unop))

/-- Canonical comparisons preserve the same original independent-family maps. -/
theorem moduleUnboundedCompactificationFamilyComparison_canonical
    (C D : Hom.DenseCompactification f) :
    moduleUnboundedCompactificationFamilyComparison f Λ hX hS models₀ models₁ N hN hΛ C ≪≫
      (@moduleUnboundedCompactificationComparison X S f _ Λ _ hX hS models₁ N hN hΛ C D) =
    (@moduleUnboundedCompactificationComparison X S f _ Λ _ hX hS models₀ N hN hΛ C D) ≪≫
      moduleUnboundedCompactificationFamilyComparison f Λ hX hS models₀ models₁ N hN hΛ D := by
  let := @moduleUnboundedCompactificationDiagram_map_isIso X S f _ Λ _ hX hS
    models₀ N hN hΛ
  let := @moduleUnboundedCompactificationDiagram_map_isIso X S f _ Λ _ hX hS
    models₁ N hN hΛ
  exact Functor.cofilteredComparison_natIso (𝟭 (Hom.DenseCompactification f))
    (moduleUnboundedCompactificationFamilyDiagramIso f Λ hX hS models₀ models₁ N hN hΛ) C D

/-- This is exactly the original three-model identity-refinement cocycle. -/
theorem moduleUnboundedCompactificationSingleModelIso_family
    (C : Hom.DenseCompactification f)
    (hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)) :
    moduleUnboundedCompactificationFamilyComparison f Λ hX hS models₀ models₁ N hN hΛ C ≪≫
      (@moduleUnboundedCompactificationSingleModelIso X S f _ Λ _ hX hS
        models₁ N hN hΛ C hC) =
    @moduleUnboundedCompactificationSingleModelIso X S f _ Λ _ hX hS
      models₀ N hN hΛ C hC := by
  apply Iso.ext
  have hc := @moduleUnboundedCompactificationMixedTransition_comp X S f _ Λ _ hX hS
    C C (𝟙 C) hC (models₁ C) C (𝟙 C) (models₀ C)
  simp only [Category.id_comp] at hc
  exact hc.symm

variable [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]

/-- The chosen family comparison is the existing original identity transition. -/
def moduleExceptionalDirectImageUnboundedFamilyComparison :
    (@moduleExceptionalDirectImageUnbounded X S _ _ f _ _ _ Λ _ hX hS (models₀
      (moduleExceptionalCompactification f))) ≅
      (@moduleExceptionalDirectImageUnbounded X S _ _ f _ _ _ Λ _ hX hS (models₁
        (moduleExceptionalCompactification f))) :=
  moduleUnboundedCompactificationFamilyComparison f Λ hX hS models₀ models₁ N hN hΛ
    (moduleExceptionalCompactification f)

/-- The actual chosen family square commutes with every supplied single value. -/
theorem moduleExceptionalUnboundedSingleValueIso_family
    (C : Hom.DenseCompactification f)
    (hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)) :
    moduleExceptionalDirectImageUnboundedFamilyComparison f Λ hX hS
        models₀ models₁ N hN hΛ ≪≫
      (@moduleExceptionalUnboundedSingleValueIso X S f _ Λ _ hX hS models₁
        N hN hΛ _ _ _ _ C hC) =
    @moduleExceptionalUnboundedSingleValueIso X S f _ Λ _ hX hS models₀
      N hN hΛ _ _ _ _ C hC :=
  isoSquarePostcompose _ _ _ _ _ _
    (moduleUnboundedCompactificationFamilyComparison_canonical f Λ hX hS models₀ models₁
      N hN hΛ (moduleExceptionalCompactification f) C)
    (moduleUnboundedCompactificationSingleModelIso_family f Λ hX hS models₀ models₁
      N hN hΛ C hC)

end AlgebraicGeometry.Scheme.EtaleCohomology
