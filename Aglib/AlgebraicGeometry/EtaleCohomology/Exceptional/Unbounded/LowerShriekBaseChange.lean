/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnboundedOpen
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleCartesianBaseChange
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactIsoCube

/-! # Original arbitrary Cartesian base change for unbounded extension by zero

The same ordinary Cartesian comparison is localized on all complexes, with the
native exact composition factors. All four derived models are independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wV wU wY wX

variable {V U Y X : Scheme.{u}} (g : V ⟶ U) (i : V ⟶ Y) (j : U ⟶ X) (f : Y ⟶ X)
  [Etale i] [Etale j] (h : IsPullback g i j f) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wV} (ModuleSheaf V Λ)]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

/-- The original exact lower-shriek Cartesian comparison on unbounded derived categories. -/
def moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso :
    moduleUnboundedDerivedLowerShriek j Λ ⋙ moduleUnboundedDerivedInverseImage Λ f ≅
      moduleUnboundedDerivedInverseImage Λ g ⋙ moduleUnboundedDerivedLowerShriek i Λ :=
  Functor.mapDerivedCategorySquareIso
    (moduleInverseImage g Λ) (moduleLowerShriek i Λ)
    (moduleLowerShriek j Λ) (moduleInverseImage f Λ)
    (moduleLowerShriekCartesianBaseChangeIso g i j f h Λ)

/-- The specified original face retains its all-complex exact-factor equation. -/
theorem moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso_fac
    (K : CochainComplex (ModuleSheaf U Λ) ℤ) :
    ExactFactorSquareEquation
      (moduleInverseImage g Λ) (moduleLowerShriek i Λ)
      (moduleLowerShriek j Λ) (moduleInverseImage f Λ)
      (TwoSquare.mk _ _ _ _ (moduleLowerShriekCartesianBaseChangeIso g i j f h Λ).hom)
      (TwoSquare.mk _ _ _ _
        (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ).hom) K :=
  mapDerivedCategorySquareIso_exactFactor
    (moduleInverseImage g Λ) (moduleLowerShriek i Λ)
    (moduleLowerShriek j Λ) (moduleInverseImage f Λ)
    (moduleLowerShriekCartesianBaseChangeIso g i j f h Λ)
    (TwoSquare.mk _ _ _ _
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ).hom) rfl K

end AlgebraicGeometry.Scheme.EtaleCohomology
