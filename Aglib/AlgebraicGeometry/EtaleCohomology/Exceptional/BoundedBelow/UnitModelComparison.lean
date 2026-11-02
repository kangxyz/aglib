/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.DirectImage
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ModelComparisonCoherence

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

/-- The literal original mixed identity map to a single supplied model. -/
def moduleCompactificationSingleModelIso (C : Hom.DenseCompactification f)
    (hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)) :
    @moduleCompactificationFunctor X S f Λ _ hX hS C (models C) ≅
      @moduleCompactificationValue X S f Λ _ hX hS C hC :=
  @asIso _ _ _ _
    (@moduleCompactificationMixedTransition X S f _ Λ _ hX hS C C (𝟙 C) hC (models C))
    (@moduleCompactificationMixedTransition_isIso X S f _ Λ _ hX hS
      C C (𝟙 C) hC (models C))

/-- The original mixed cocycle gives the actual single-model refinement square. -/
theorem moduleCompactificationSingleModelIso_refinement
    {C D : Hom.DenseCompactification f} (a : C ⟶ D)
    (hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ))
    (hD : HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)) :
    moduleCompactificationTransition Λ a ≫ (moduleCompactificationSingleModelIso f Λ C hC).hom =
      (moduleCompactificationSingleModelIso f Λ D hD).hom ≫
        (@moduleCompactificationMixedTransition X S f _ Λ _ hX hS C D a hC hD) := by
  have h₀ := @moduleCompactificationMixedTransition_comp X S f _ Λ _ hX hS
    C C (𝟙 C) hC (models C) D a (models D)
  have h₁ := @moduleCompactificationMixedTransition_comp X S f _ Λ _ hX hS
    C D a hC hD D (𝟙 D) (models D)
  simp only [Category.id_comp, Category.comp_id] at h₀ h₁
  exact h₀.symm.trans h₁

variable [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]

/-- Canonical comparison with any single original value, retaining its supplied native model. -/
def moduleExceptionalSingleValueIso (C : Hom.DenseCompactification f)
    (hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)) :
    @moduleExceptionalDirectImagePlus X S _ _ f _ _ _ Λ _ hX hS
        (models (moduleExceptionalCompactification f)) ≅
      @moduleCompactificationValue X S f Λ _ hX hS C hC :=
  moduleExceptionalDirectImagePlusIso f Λ C ≪≫ moduleCompactificationSingleModelIso f Λ C hC

/-- The original chosen comparison follows the actual refinement transition. -/
theorem moduleExceptionalDirectImagePlusIso_refinement
    {C D : Hom.DenseCompactification f} (a : C ⟶ D) :
    moduleExceptionalDirectImagePlusIso f Λ D ≪≫ asIso (moduleCompactificationTransition Λ a) =
      moduleExceptionalDirectImagePlusIso f Λ C := by
  have hc : asIso (moduleCompactificationTransition Λ a) =
      moduleCompactificationComparison f Λ D C := by
    rw [← moduleCompactificationComparison_symm f Λ C D,
      moduleCompactificationComparison_refinement f Λ a]
    exact (Iso.symm_symm_eq _).symm
  rw [hc]
  exact moduleExceptionalDirectImagePlusIso_trans f Λ D C

/-- Refinement compatibility is proved from the original cocycle. -/
theorem moduleExceptionalSingleValueIso_refinement
    {C D : Hom.DenseCompactification f} (a : C ⟶ D)
    (hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ))
    (hD : HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)) :
    (moduleExceptionalSingleValueIso f Λ D hD).hom ≫
      (@moduleCompactificationMixedTransition X S f _ Λ _ hX hS C D a hC hD) =
    (moduleExceptionalSingleValueIso f Λ C hC).hom := by
  have hs := moduleCompactificationSingleModelIso_refinement f Λ a hC hD
  have hc := congrArg Iso.hom (moduleExceptionalDirectImagePlusIso_refinement f Λ a)
  change (moduleExceptionalDirectImagePlusIso f Λ D).hom ≫
    moduleCompactificationTransition Λ a = (moduleExceptionalDirectImagePlusIso f Λ C).hom at hc
  change ((moduleExceptionalDirectImagePlusIso f Λ D).hom ≫
    (moduleCompactificationSingleModelIso f Λ D hD).hom) ≫ _ =
    (moduleExceptionalDirectImagePlusIso f Λ C).hom ≫
      (moduleCompactificationSingleModelIso f Λ C hC).hom
  rw [Category.assoc, ← hs, ← Category.assoc, hc]

end AlgebraicGeometry.Scheme.EtaleCohomology
