/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.HomologicalComplex.Adjunction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Aglib.CategoryTheory.Localization.AdjunctionMate

/-! # Original exact adjunctions on the unbounded derived category -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w u' v' w'

namespace CategoryTheory.Adjunction

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- The exact left adjoint on cochain complexes commutes with derived localization
through its original comparison isomorphism. -/
local instance leftLocalizationSquare :
    CatCommSq (L.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q DerivedCategory.Q
      L.mapDerivedCategory := ⟨L.mapDerivedCategoryFactors.symm⟩

/-- The exact right adjoint on cochain complexes commutes with derived localization
through its original comparison isomorphism. -/
local instance rightLocalizationSquare :
    CatCommSq (R.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q DerivedCategory.Q
      R.mapDerivedCategory := ⟨R.mapDerivedCategoryFactors.symm⟩

/-- Localization of the original cochain adjunction when both adjoints are exact. -/
def mapDerivedCategoryAdjunction : L.mapDerivedCategory ⊣ R.mapDerivedCategory :=
  (adj.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso D (.up ℤ))
    L.mapDerivedCategory R.mapDerivedCategory

/-- The original exact localization factors are mates. -/
theorem mapDerivedCategoryAdjunction_factor_mate :
    (mateEquiv (adj.mapHomologicalComplex (.up ℤ)) adj.mapDerivedCategoryAdjunction
      (TwoSquare.mk _ _ _ _ L.mapDerivedCategoryFactors.hom)).natTrans =
      R.mapDerivedCategoryFactors.inv :=
  (adj.mapHomologicalComplex (.up ℤ)).localization_factor_mate
    DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso D (.up ℤ))
    L.mapDerivedCategory R.mapDerivedCategory

end CategoryTheory.Adjunction
