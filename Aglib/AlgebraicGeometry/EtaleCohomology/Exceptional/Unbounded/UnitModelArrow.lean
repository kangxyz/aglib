/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.UnitModelFamily
public import Aglib.AlgebraicGeometry.Compactification.Refinements.ArrowEquality

/-! # Original arrow equality and independent unbounded model-family transport

Equality elimination transports only the original scheme arrow. At reflexivity,
the map is the original identity-refinement family comparison, not a comparison
defined using a composition coherence conclusion.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM₀ wM₁ wC
variable {X S : Scheme.{u}} {f g : X ⟶ S} [QuasiCompact f] [QuasiCompact g]
  [CompactSpace S] [QuasiSeparatedSpace S]
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
  (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)) (e : f = g)
  (models₀ : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM₀} (ModuleSheaf C.Xbar Λ))
  (models₁ : ∀ C : Hom.DenseCompactification g,
    HasDerivedCategory.{wM₁} (ModuleSheaf C.Xbar Λ))
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- Original arrow equality followed by the original mixed-model identity comparison. -/
def moduleExceptionalDirectImageUnboundedCongr :
    (@moduleExceptionalDirectImageUnbounded X S _ _ f _ _ _ Λ _ hX hS (models₀
      (moduleExceptionalCompactification f))) ≅
      (@moduleExceptionalDirectImageUnbounded X S _ _ g _ _ _ Λ _ hX hS (models₁
        (moduleExceptionalCompactification g))) := by
  subst g
  exact moduleExceptionalDirectImageUnboundedFamilyComparison f Λ hX hS
    models₀ models₁ N hN hΛ

/-- The original arrow-plus-family map preserves the same independently supplied value. -/
theorem moduleExceptionalUnboundedSingleValueIso_congr
    (C : Hom.DenseCompactification f)
    (hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)) :
    moduleExceptionalDirectImageUnboundedCongr Λ hX hS e models₀ models₁ N hN hΛ ≪≫
      (moduleExceptionalUnboundedSingleValueIso (hX := hX) (hS := hS) (models := models₁)
        g Λ N hN hΛ (Hom.DenseCompactification.ofArrowEq e C) hC) =
    moduleExceptionalUnboundedSingleValueIso (hX := hX) (hS := hS) (models := models₀)
      f Λ N hN hΛ C hC := by
  subst g
  exact moduleExceptionalUnboundedSingleValueIso_family f Λ hX hS models₀ models₁
    N hN hΛ C hC

end AlgebraicGeometry.Scheme.EtaleCohomology
