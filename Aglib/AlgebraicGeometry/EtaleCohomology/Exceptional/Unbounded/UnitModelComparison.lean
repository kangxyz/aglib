/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.DirectImage
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.MixedModelTransition

/-! # Canonical comparison with one independently modeled compactification

Only the supplied compactification receives its supplied model. No global
family is modified to force an identity ambient to use the endpoint model.
All comparison maps are the original mixed identity-refinement transitions.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM wC wD
variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [models : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The literal original mixed identity map to a single supplied model. -/
def moduleUnboundedCompactificationSingleModelIso (C : Hom.DenseCompactification f)
    (hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)) :
    @moduleUnboundedCompactificationFunctor X S f Λ _ hX hS C (models C) ≅
      @moduleUnboundedCompactificationFunctor X S f Λ _
      hX hS C hC :=
  @asIso _ _ _ _
    (@moduleUnboundedCompactificationMixedTransition X S f _ Λ _ hX hS C C (𝟙 C) hC (models C))
    (@moduleUnboundedCompactificationMixedTransition_isIso X S f _ Λ _ hX hS
      C C (𝟙 C) hC (models C) N hN hΛ)

/-- The original mixed cocycle gives the actual single-model refinement square. -/
theorem moduleUnboundedCompactificationSingleModelIso_refinement
    {C D : Hom.DenseCompactification f} (a : C ⟶ D)
    (hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ))
    (hD : HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)) :
    moduleUnboundedCompactificationTransition Λ a ≫ (moduleUnboundedCompactificationSingleModelIso f
      Λ N hN hΛ C hC).hom =
      (moduleUnboundedCompactificationSingleModelIso f Λ N hN hΛ D hD).hom ≫
        (@moduleUnboundedCompactificationMixedTransition X S f _ Λ _ hX hS C D a hC hD) := by
  have h₀ := @moduleUnboundedCompactificationMixedTransition_comp X S f _ Λ _ hX hS
    C C (𝟙 C) hC (models C) D a (models D)
  have h₁ := @moduleUnboundedCompactificationMixedTransition_comp X S f _ Λ _ hX hS
    C D a hC hD D (𝟙 D) (models D)
  simp only [Category.id_comp, Category.comp_id] at h₀ h₁
  exact h₀.symm.trans h₁

variable [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]

/-- Canonical comparison with any single original value, retaining its supplied native model. -/
def moduleExceptionalUnboundedSingleValueIso (C : Hom.DenseCompactification f)
    (hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)) :
    @moduleExceptionalDirectImageUnbounded X S _ _ f _ _ _ Λ _ hX hS
        (models (moduleExceptionalCompactification f)) ≅
      @moduleUnboundedCompactificationFunctor X S f Λ _ hX
      hS C hC :=
  moduleExceptionalDirectImageUnboundedIso f Λ N hN hΛ C ≪≫
    moduleUnboundedCompactificationSingleModelIso f Λ N hN hΛ C hC

/-- Refinement compatibility is proved from the original cocycle. -/
theorem moduleExceptionalUnboundedSingleValueIso_refinement
    {C D : Hom.DenseCompactification f} (a : C ⟶ D)
    (hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ))
    (hD : HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)) :
    (moduleExceptionalUnboundedSingleValueIso f Λ N hN hΛ D hD).hom ≫
      (@moduleUnboundedCompactificationMixedTransition X S f _ Λ _ hX hS C D a hC hD) =
    (moduleExceptionalUnboundedSingleValueIso f Λ N hN hΛ C hC).hom := by
  have hs := moduleUnboundedCompactificationSingleModelIso_refinement f Λ N hN hΛ a hC hD
  have hc := congrArg Iso.hom (moduleExceptionalDirectImageUnboundedIso_refinement f Λ N hN hΛ a)
  change (moduleExceptionalDirectImageUnboundedIso f Λ N hN hΛ D).hom ≫
    moduleUnboundedCompactificationTransition Λ a = (moduleExceptionalDirectImageUnboundedIso f Λ N
      hN hΛ C).hom at hc
  change ((moduleExceptionalDirectImageUnboundedIso f Λ N hN hΛ D).hom ≫
    (moduleUnboundedCompactificationSingleModelIso f Λ N hN hΛ D hD).hom) ≫ _ =
    (moduleExceptionalDirectImageUnboundedIso f Λ N hN hΛ C).hom ≫
      (moduleUnboundedCompactificationSingleModelIso f Λ N hN hΛ C hC).hom
  rw [Category.assoc, ← hs, ← Category.assoc, hc]

end AlgebraicGeometry.Scheme.EtaleCohomology
