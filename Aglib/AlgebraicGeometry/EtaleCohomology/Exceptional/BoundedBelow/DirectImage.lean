/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.Independence

/-!
# A choice-independent bounded-below exceptional direct image

A chosen actual Nagata compactification defines the functor, and canonical
comparisons with every other compactification, with their cocycle and actual
refinement equations, make this construction independent of that choice.
This first endpoint has torsion input and ambient D+ output. Torsion-valued
output, functorial composition in the scheme map and arbitrary exceptional
base change are separate subsequent statements.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wM

variable {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
  (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- An actual schematically dense Nagata compactification, whose choice is
removed from the functorial result by the canonical comparison API. -/
def moduleExceptionalCompactification : Hom.DenseCompactification f :=
  Classical.choice inferInstance

variable (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

section Value

variable [HasDerivedCategory.{wM}
  (ModuleSheaf (moduleExceptionalCompactification f).Xbar Λ)]

/-- Bounded-below exceptional direct image on original torsion-cohomology input,
with its original ambient bounded-below derived target. -/
def moduleExceptionalDirectImagePlus :
    (moduleTorsionCohomologyPlus X Λ).FullSubcategory ⥤
      DerivedCategory.Plus (ModuleSheaf S Λ) :=
  moduleCompactificationFunctor f Λ (moduleExceptionalCompactification f)

end Value

variable [middleModels : ∀ C : Hom.DenseCompactification f,
  HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- Canonical comparison of the exceptional functor with every actual compactification. -/
def moduleExceptionalDirectImagePlusIso (C : Hom.DenseCompactification f) :
    moduleExceptionalDirectImagePlus f Λ ≅ moduleCompactificationFunctor f Λ C :=
  moduleCompactificationComparison f Λ (moduleExceptionalCompactification f) C

/-- Changing compactification uses the same choice-independent cocycle. -/
theorem moduleExceptionalDirectImagePlusIso_trans (C D : Hom.DenseCompactification f) :
    moduleExceptionalDirectImagePlusIso f Λ C ≪≫ moduleCompactificationComparison f Λ C D =
      moduleExceptionalDirectImagePlusIso f Λ D :=
  moduleCompactificationComparison_trans f Λ (moduleExceptionalCompactification f) C D

/-- Comparison with the compactification used in the definition is the identity. -/
@[simp]
theorem moduleExceptionalDirectImagePlusIso_self :
    moduleExceptionalDirectImagePlusIso f Λ (moduleExceptionalCompactification f) = Iso.refl _ :=
  moduleCompactificationComparison_self f Λ (moduleExceptionalCompactification f)

end AlgebraicGeometry.Scheme.EtaleCohomology
