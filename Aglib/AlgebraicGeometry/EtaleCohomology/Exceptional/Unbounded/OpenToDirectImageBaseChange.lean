/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.LowerShriekBaseChangeMate
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChangePasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenToDirectImage
public import Aglib.CategoryTheory.Adjunction.TripleBaseChange

/-! # The original canonical open comparison respects actual Cartesian base change -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wV wU wY wX
variable (Λ : Type (u + 1)) [Ring Λ] {V U Y X : Scheme.{u}}
  (g : V ⟶ U) (i : V ⟶ Y) (j : U ⟶ X) (f : Y ⟶ X)
  [IsOpenImmersion i] [IsOpenImmersion j] (h : IsPullback g i j f)
  [HasDerivedCategory.{wV} (ModuleSheaf V Λ)]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

/-- Both original Cartesian exchanges preserve the same canonical triple maps. -/
theorem moduleUnboundedLowerShriekToDirectImage_baseChange :
    Adjunction.TripleBaseChangeEquation (moduleUnboundedOpenTriple Λ j)
      (moduleUnboundedOpenTriple Λ i) (moduleUnboundedDerivedInverseImage Λ f)
      (moduleUnboundedDerivedInverseImage Λ g)
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ)
      (moduleUnboundedDerivedBaseChangeMap Λ j i f g h.w.symm) := by
  apply Adjunction.Triple.leftToRight_baseChange
    (moduleUnboundedOpenTriple Λ j) (moduleUnboundedOpenTriple Λ i)
    (moduleUnboundedDerivedInverseImage Λ f) (moduleUnboundedDerivedInverseImage Λ g)
    (moduleUnboundedDerivedInverseImageSquareIso Λ f g j i h.w)
  · ext K
    exact congrArg (fun t => t.app K)
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso_inv_mate g i j f h Λ)
  · dsimp only [moduleUnboundedDerivedBaseChangeMap]
    rw [moduleUnboundedDerivedInverseImageSquareIso_transpose Λ f g j i h.w]
    rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
