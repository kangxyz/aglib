/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ToDirectImageNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenIsomorphism
public import Aglib.AlgebraicGeometry.Compactification.Refinements.CompositionUnits

/-! # Proper normalization of the same canonical unbounded exceptional map -/
@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [middleModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- The literal proper factorization contracts by its original canonical identity map. -/
def moduleUnboundedProperCompactificationNormalizationIso :
    moduleUnboundedCompactificationFunctor f Λ (Hom.DenseCompactification.ofProper f) ≅
      moduleUnboundedDerivedDirectImage Λ f := by
  let C := Hom.DenseCompactification.ofProper f
  letI : IsIso C.j := inferInstanceAs (IsIso (𝟙 X))
  haveI : IsIso (moduleUnboundedLowerShriekToDirectImage Λ C.j) :=
    moduleUnboundedLowerShriekToDirectImage_isIso_of_isIso Λ C.j
  exact Functor.isoWhiskerRight (asIso (moduleUnboundedLowerShriekToDirectImage Λ C.j))
      (moduleUnboundedDerivedDirectImage Λ C.p) ≪≫
    moduleUnboundedDerivedDirectImageOverIso Λ f C.p C.j C.fac

/-- The proper normalization is literally the same original comparison map. -/
theorem moduleUnboundedProperCompactificationNormalizationIso_hom :
    (moduleUnboundedProperCompactificationNormalizationIso f Λ).hom =
      moduleUnboundedCompactificationToDirectImage f Λ (Hom.DenseCompactification.ofProper f) := rfl

variable [CompactSpace S] [QuasiSeparatedSpace S]
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The chosen proper normalization uses its actual comparison with the literal proper model. -/
def moduleExceptionalUnboundedProperNormalizationIso :
    moduleExceptionalDirectImageUnbounded f Λ ≅ moduleUnboundedDerivedDirectImage Λ f :=
  moduleExceptionalDirectImageUnboundedIso f Λ N hN hΛ (Hom.DenseCompactification.ofProper f) ≪≫
    moduleUnboundedProperCompactificationNormalizationIso f Λ

/-- The chosen normalization equals the same canonical exceptional-to-ordinary map. -/
theorem moduleExceptionalUnboundedProperNormalizationIso_hom :
    (moduleExceptionalUnboundedProperNormalizationIso f Λ N hN hΛ).hom =
      moduleExceptionalToDirectImageUnbounded f Λ :=
  moduleExceptionalToDirectImageUnbounded_model f Λ N hN hΛ
    (Hom.DenseCompactification.ofProper f)
end AlgebraicGeometry.Scheme.EtaleCohomology
