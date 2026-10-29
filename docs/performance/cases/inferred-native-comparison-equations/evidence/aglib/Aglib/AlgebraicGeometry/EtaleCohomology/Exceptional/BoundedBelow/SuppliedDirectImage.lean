/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.Independence

/-!
# Supplied compactifiability and the original unary exceptional value

The source is the native torsion full subcategory; the target is ambient D+.
The value uses only the chosen compactification's middle realization. The
consistent family is needed only to compare actual compactifications.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wM

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  [Nonempty (Hom.DenseCompactification f)]

/-- Choose one actual compactification from the supplied nonempty category. -/
def moduleExceptionalSuppliedCompactification : Hom.DenseCompactification f :=
  Classical.choice inferInstance

variable (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

section Value

variable [HasDerivedCategory.{wM}
  (ModuleSheaf (moduleExceptionalSuppliedCompactification f).Xbar Λ)]

/-- The original open-extension/proper-image value with the chosen middle model only. -/
def moduleExceptionalDirectImagePlusOfNonempty :
    (moduleTorsionCohomologyPlus X Λ).FullSubcategory ⥤
      DerivedCategory.Plus (ModuleSheaf S Λ) :=
  moduleCompactificationFunctor f Λ (moduleExceptionalSuppliedCompactification f)

end Value

section Comparison

variable [middleModels : ∀ C : Hom.DenseCompactification f,
  HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- The actual consistent family gives the canonical comparison with every compactification. -/
def moduleExceptionalDirectImagePlusOfNonemptyIso (C : Hom.DenseCompactification f) :
    moduleExceptionalDirectImagePlusOfNonempty f Λ ≅ moduleCompactificationFunctor f Λ C :=
  moduleCompactificationComparison f Λ (moduleExceptionalSuppliedCompactification f) C

/-- The canonical comparisons retain their actual cocycle equation. -/
theorem moduleExceptionalDirectImagePlusOfNonemptyIso_trans (C D : Hom.DenseCompactification f) :
    moduleExceptionalDirectImagePlusOfNonemptyIso f Λ C ≪≫
      moduleCompactificationComparison f Λ C D =
        moduleExceptionalDirectImagePlusOfNonemptyIso f Λ D :=
  moduleCompactificationComparison_trans f Λ (moduleExceptionalSuppliedCompactification f) C D

end Comparison

end AlgebraicGeometry.Scheme.EtaleCohomology
