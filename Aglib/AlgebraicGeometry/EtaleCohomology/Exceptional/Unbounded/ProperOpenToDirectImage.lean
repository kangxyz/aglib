/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperOpenMate
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenToDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.DirectImageSquare
public import Aglib.CategoryTheory.Adjunction.TripleMateStructural

/-! # The original unbounded mixed mate preserves the canonical outer-adjoint maps -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wV wU wY wX
variable {V U Y X : Scheme.{u}} (g : V ⟶ U) (i : V ⟶ Y) (j : U ⟶ X) (f : Y ⟶ X)
  [IsOpenImmersion i] [IsOpenImmersion j] (h : IsPullback g i j f)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wV} (ModuleSheaf V Λ)]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

/-- The two original mates preserve the actual canonical triple comparisons. -/
theorem moduleUnboundedProperOpenMate_toDirectImage :
    Adjunction.TripleMateCompatibilityEquation
      (moduleUnboundedOpenTriple Λ j) (moduleUnboundedOpenTriple Λ i)
      (moduleUnboundedCartesianExchangeIso g i j f h Λ)
      (moduleUnboundedProperOpenMate g i j f h Λ) :=
  Adjunction.tripleMateCompatibilityEquation _ _ _ _
    (Adjunction.tripleMateTransposeEquation _ _ _
      (moduleUnboundedDerivedAdjunction Λ f) (moduleUnboundedDerivedAdjunction Λ g)
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ).hom
      (conjugateEquiv_moduleUnboundedLowerShriekCartesianBaseChangeIso_hom g i j f h Λ))

/-- The right comparison is the actual native structural direct-image square. -/
theorem moduleUnboundedProperOpenMate_toDirectImageSquare :
    Adjunction.TripleMateStructuralEquation
      (moduleUnboundedOpenTriple Λ j) (moduleUnboundedOpenTriple Λ i)
      (moduleUnboundedProperOpenMate g i j f h Λ)
      (moduleUnboundedDerivedDirectImageSquareIso Λ f g j i h.w).hom :=
  Adjunction.tripleMateStructuralEquation _ _
    (moduleUnboundedCartesianExchangeIso g i j f h Λ) _ _
    (moduleUnboundedProperOpenMate_toDirectImage g i j f h Λ)
    (mate_moduleUnboundedDerivedBaseChangeMap Λ f g j i h.w)
end AlgebraicGeometry.Scheme.EtaleCohomology
