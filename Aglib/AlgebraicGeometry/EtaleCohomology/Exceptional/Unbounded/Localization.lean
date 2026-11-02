/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.DirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.Unbounded

/-! # Actual unbounded localization after the selected exceptional direct image -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wU wZ wX wS wM
variable {X S U Z : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
  (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [middleModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  (j : U ⟶ X) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
  (hcomp : Set.range j = (Set.range i)ᶜ)
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]

/-- The specified chosen functor retains the native composite shift structure. -/
instance moduleExceptionalDirectImageUnboundedCommShift :
    (moduleExceptionalDirectImageUnbounded f Λ).CommShift ℤ :=
  inferInstanceAs ((moduleUnboundedDerivedLowerShriek
    (moduleExceptionalCompactification f).j Λ ⋙ moduleUnboundedDerivedDirectImage Λ
      (moduleExceptionalCompactification f).p).CommShift ℤ)

/-- The specified chosen functor is the native triangulated composite. -/
instance moduleExceptionalDirectImageUnbounded_isTriangulated :
    (moduleExceptionalDirectImageUnbounded f Λ).IsTriangulated :=
  inferInstanceAs ((moduleUnboundedDerivedLowerShriek
    (moduleExceptionalCompactification f).j Λ ⋙ moduleUnboundedDerivedDirectImage Λ
      (moduleExceptionalCompactification f).p).IsTriangulated)

/-- Apply the chosen actual functor to the original triangle, including its connecting map. -/
def moduleExceptionalUnboundedLocalizationRawTriangle
    (K : DerivedCategory (ModuleSheaf X Λ)) :
    Triangle (DerivedCategory (ModuleSheaf S Λ)) :=
  (moduleExceptionalDirectImageUnbounded f Λ).mapTriangle.obj
    (moduleUnboundedDerivedLocalizationTriangle j Λ i hcomp K)

/-- The actual unbounded triangulated functor preserves the original distinguished triangle. -/
theorem moduleExceptionalUnboundedLocalizationRawTriangle_distinguished
    (K : DerivedCategory (ModuleSheaf X Λ)) :
    moduleExceptionalUnboundedLocalizationRawTriangle f Λ j i hcomp K ∈
      distTriang (DerivedCategory (ModuleSheaf S Λ)) :=
  (moduleExceptionalDirectImageUnbounded f Λ).map_distinguished _
    (moduleUnboundedDerivedLocalizationTriangle_distinguished j Λ i hcomp K)
end AlgebraicGeometry.Scheme.EtaleCohomology
