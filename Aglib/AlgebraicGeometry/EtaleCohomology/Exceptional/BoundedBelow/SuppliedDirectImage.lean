/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.Torsion
public import Aglib.AlgebraicGeometry.Compactification.Refinements.Supplied

/-!
# Supplied compactifiability and the original unary exceptional value

The ambient value and its torsion-valued lift use only the chosen
compactification's actual middle realization. The lift uses the existing
proper direct-image preservation theorem and keeps the original underlying
functor. A consistent family is needed only for comparisons with other
compactifications and with the earlier Nagata endpoint.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wM

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  [Nonempty (Hom.DenseCompactification f)]

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

/-- The same chosen value lands in native torsion, using only its own middle model. -/
def moduleExceptionalDirectImagePlusTorsionOfNonempty :
    (moduleTorsionCohomologyPlus X Λ).FullSubcategory ⥤
      (moduleTorsionCohomologyPlus S Λ).FullSubcategory :=
  moduleCompactificationTorsionFunctor f Λ (moduleExceptionalSuppliedCompactification f)

/-- Forgetting target torsion retains the literal underlying chosen functor. -/
def moduleExceptionalDirectImagePlusTorsionOfNonemptyForgetIso :
    moduleExceptionalDirectImagePlusTorsionOfNonempty f Λ ⋙ (moduleTorsionCohomologyPlus S Λ).ι ≅
      moduleExceptionalDirectImagePlusOfNonempty f Λ :=
  moduleCompactificationTorsionForgetIso f Λ (moduleExceptionalSuppliedCompactification f)

end Value

section Comparison

variable [middleModels : ∀ C : Hom.DenseCompactification f,
  HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- The actual consistent family gives the canonical comparison with every compactification. -/
def moduleExceptionalDirectImagePlusOfNonemptyIso (C : Hom.DenseCompactification f) :
    moduleExceptionalDirectImagePlusOfNonempty f Λ ≅ moduleCompactificationFunctor f Λ C :=
  moduleCompactificationComparison f Λ (moduleExceptionalSuppliedCompactification f) C

/-- The target-torsion comparison retains the original canonical underlying map. -/
def moduleExceptionalDirectImagePlusTorsionOfNonemptyIso (C : Hom.DenseCompactification f) :
    moduleExceptionalDirectImagePlusTorsionOfNonempty f Λ ≅
      moduleCompactificationTorsionFunctor f Λ C :=
  moduleCompactificationTorsionComparison f Λ (moduleExceptionalSuppliedCompactification f) C

/-- The canonical comparisons retain their actual cocycle equation. -/
theorem moduleExceptionalDirectImagePlusOfNonemptyIso_trans (C D : Hom.DenseCompactification f) :
    moduleExceptionalDirectImagePlusOfNonemptyIso f Λ C ≪≫
      moduleCompactificationComparison f Λ C D =
        moduleExceptionalDirectImagePlusOfNonemptyIso f Λ D :=
  moduleCompactificationComparison_trans f Λ (moduleExceptionalSuppliedCompactification f) C D

variable [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]

/-- With the same middle family, the supplied value is the original Nagata value. -/
theorem moduleExceptionalDirectImagePlusOfNonempty_eq :
    moduleExceptionalDirectImagePlusOfNonempty f Λ = moduleExceptionalDirectImagePlus f Λ := rfl

/-- The same choice and middle-family entry also identify the original torsion lift. -/
theorem moduleExceptionalDirectImagePlusTorsionOfNonempty_eq :
    moduleExceptionalDirectImagePlusTorsionOfNonempty f Λ =
      moduleExceptionalDirectImagePlusTorsion f Λ := rfl

end Comparison

end AlgebraicGeometry.Scheme.EtaleCohomology
