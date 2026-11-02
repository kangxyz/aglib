/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenComparisonCube
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.ToDirectImageCompatibility
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
theorem moduleDerivedLowerShriekToDirectImage_baseChange :
    Adjunction.TripleBaseChangeEquation (moduleDerivedOpenTriple Λ j)
      (moduleDerivedOpenTriple Λ i) (moduleDerivedInverseImage Λ f)
      (moduleDerivedInverseImage Λ g)
      (moduleDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ)
      (moduleDerivedBaseChangeMap Λ j i f g h.w.symm) := by
  apply Adjunction.Triple.leftToRight_baseChange
    (moduleDerivedOpenTriple Λ j) (moduleDerivedOpenTriple Λ i)
    (moduleDerivedInverseImage Λ f) (moduleDerivedInverseImage Λ g)
    (moduleDerivedInverseImageSquareIso Λ f g j i h.w)
  · exact mateEquiv_moduleDerivedOpenComparison_inv g i j f h Λ
  · dsimp only [moduleDerivedBaseChangeMap]
    rw [moduleDerivedInverseImageSquareIso_transpose Λ f g j i h.w]
    rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
