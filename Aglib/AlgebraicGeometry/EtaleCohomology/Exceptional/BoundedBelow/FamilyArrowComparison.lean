/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.FamilyCongruence
public import Aglib.AlgebraicGeometry.Compactification.Refinements.ArrowEquality

/-! # Original arrow equality commutes with canonical compactification comparisons -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM
variable {X S : Scheme.{u}} {f g : X ⟶ S}
  (Λ : Type (u + 1)) [Ring Λ] (e : f = g)
  (models : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))

/-- The reindexed family retains the original model on the literal transported ambient. -/
theorem moduleCompactificationModelFamilyCongr_apply (C : Hom.DenseCompactification f) :
    moduleCompactificationModelFamilyCongr Λ e models
        (Hom.DenseCompactification.ofArrowEq e C) = models C := by
  subst g
  rfl

variable [QuasiCompact f] [QuasiCompact g]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ))

/-- Literal arrow transport of the original compactification value. -/
def moduleCompactificationTorsionArrowIso (C : Hom.DenseCompactification f) :
    (@moduleCompactificationTorsionFunctor X S f Λ _ hX hS C (models C)) ≅
      (@moduleCompactificationTorsionFunctor X S g Λ _ hX hS
        (Hom.DenseCompactification.ofArrowEq e C)
        (moduleCompactificationModelFamilyCongr Λ e models
          (Hom.DenseCompactification.ofArrowEq e C))) := by
  subst g
  exact Iso.refl _

variable [CompactSpace S] [QuasiSeparatedSpace S]
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]

/-- Original equality transport commutes with every actual canonical compactification comparison. -/
theorem moduleExceptionalDirectImagePlusTorsionArrowIso_model
    (C : Hom.DenseCompactification f) :
    moduleExceptionalDirectImagePlusTorsionArrowIso Λ hX hS e models ≪≫
      (@moduleExceptionalDirectImagePlusTorsionIso X S g _ Λ _ hX hS
        _ _ _ _ (moduleCompactificationModelFamilyCongr Λ e models)
        (Hom.DenseCompactification.ofArrowEq e C)) =
    (@moduleExceptionalDirectImagePlusTorsionIso X S f _ Λ _ hX hS _ _ _ _ models C) ≪≫
      moduleCompactificationTorsionArrowIso Λ e models hX hS C := by
  subst g
  simp only [moduleExceptionalDirectImagePlusTorsionArrowIso,
    moduleCompactificationTorsionArrowIso, Iso.refl_trans]
  change (@moduleExceptionalDirectImagePlusTorsionIso X S f _ Λ _ hX hS _ _ _ _ models C) = _
  exact (Iso.trans_refl _).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
