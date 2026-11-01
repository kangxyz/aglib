/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.UnitModelComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ToDirectImageNaturality

/-! # Original single-value comparisons preserve the canonical ordinary-image map -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM wC wD
variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

/-- A single model retains exactly the original outer-adjoint map and structural triangle. -/
def moduleUnboundedSingleValueToDirectImage (C : Hom.DenseCompactification f)
    [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)] :
    moduleUnboundedCompactificationFunctor f Λ C ⟶ moduleUnboundedDerivedDirectImage Λ f :=
  Functor.whiskerRight (moduleUnboundedLowerShriekToDirectImage Λ C.j)
      (moduleUnboundedDerivedDirectImage Λ C.p) ≫
    (moduleUnboundedDerivedDirectImageOverIso Λ f C.p C.j C.fac).hom

/-- The original mixed refinement square also preserves the canonical target map. -/
theorem moduleUnboundedSingleValueToDirectImage_refinement
    {C D : Hom.DenseCompactification f} (a : C ⟶ D)
    [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
    [HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)] :
    TargetComparisonEquation (moduleUnboundedCompactificationMixedTransition Λ a)
      (moduleUnboundedSingleValueToDirectImage Λ C)
      (moduleUnboundedSingleValueToDirectImage Λ D) :=
  imageComparison_toTarget_equation
    (moduleUnboundedDerivedRefinementComparison a Λ)
    (moduleUnboundedLowerShriekToDirectImage Λ C.j)
    (moduleUnboundedLowerShriekToDirectImage Λ D.j)
    (moduleUnboundedDerivedDirectImageOverIso Λ D.j a.hom C.j a.open_fac)
    (moduleUnboundedDerivedRefinementDirectImageIso Λ a)
    (moduleUnboundedDerivedDirectImageOverIso Λ f C.p C.j C.fac)
    (moduleUnboundedDerivedDirectImageOverIso Λ f D.p D.j D.fac)
    (moduleUnboundedDerivedProperRefinementComparison_toDirectImage_naturality
      Λ C.j D.j a.hom (Hom.DenseCompactification.isPullback_open a))
    (moduleUnboundedDerivedDirectImageOverIso_triangle Λ f C.j D.j a.hom C.p D.p
      a.open_fac a.base_fac C.fac D.fac)

variable (f) [models : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)
  [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]

/-- Canonical comparison with any independently supplied value preserves the original map. -/
theorem moduleExceptionalUnboundedSingleValueIso_toDirectImage
    (C : Hom.DenseCompactification f)
    (hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)) :
    (moduleExceptionalUnboundedSingleValueIso f Λ N hN hΛ C hC).hom ≫
      (@moduleUnboundedSingleValueToDirectImage X S f Λ _ hX hS C hC) =
      moduleExceptionalToDirectImageUnbounded f Λ := by
  have hm := @moduleUnboundedSingleValueToDirectImage_refinement X S f _ Λ _ hX hS
    C C (𝟙 C) hC (models C)
  have hc := moduleExceptionalToDirectImageUnbounded_model f Λ N hN hΛ C
  change ((moduleExceptionalDirectImageUnboundedIso f Λ N hN hΛ C).hom ≫
    (moduleUnboundedCompactificationSingleModelIso f Λ N hN hΛ C hC).hom) ≫ _ = _
  rw [Category.assoc]
  have he := congrArg
    (fun t => (moduleExceptionalDirectImageUnboundedIso f Λ N hN hΛ C).hom ≫ t) hm
  exact he.trans hc

end AlgebraicGeometry.Scheme.EtaleCohomology
