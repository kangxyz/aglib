/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleRefinementCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleCartesianExchangeMate
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactMate
public import Aglib.CategoryTheory.Adjunction.TwoSidedMateIsomorphism

/-! # Original unbounded exchange along etale charts

The actual exchange for an etale base change, including open restriction, is
invertible without properness or a cohomological bound. The proof localizes the
original exact lower-shriek mate on all complexes and then uses the original
iterated adjunction-mate equation. No replacement is assumed to have torsion
terms, and no equality is inferred from homology or bounded-below testing.
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

omit [HasDerivedCategory.{wV} (ModuleSheaf V Λ)]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)] in
/-- The inverse original lower-shriek square is the actual vertical mate of
the same original inverse-image square. -/
theorem moduleLowerShriekCartesianBaseChangeIso_inv_mate :
    (mateEquiv (moduleLowerShriekAdjunction j Λ) (moduleLowerShriekAdjunction i Λ)
      (TwoSquare.mk _ _ _ _ (moduleLowerShriekCartesianBaseChangeIso g i j f h Λ).inv)).natTrans =
      (moduleInverseImageSquareIso Λ f g j i h.w).hom :=
  mateEquiv_inv_eq_of_conjugate
    (moduleLowerShriekAdjunction j Λ) (moduleLowerShriekAdjunction i Λ)
    (moduleInverseImageAdjunction g Λ) (moduleInverseImageAdjunction f Λ)
    (moduleLowerShriekCartesianBaseChangeIso g i j f h Λ)
    (moduleCartesianExchangeIso g i j f h Λ)
    (moduleInverseImageSquareIso Λ f g j i h.w).hom
    (conjugateEquiv_moduleLowerShriekCartesianBaseChangeIso_hom g i j f h Λ)
    (moduleCartesianExchangeIso_hom g i j f h Λ).symm

/-- Open or etale base change makes the actual original unbounded exchange
invertible for an arbitrary coefficient ring and every unbounded object. -/
theorem moduleUnboundedDerivedBaseChange_isIso_of_etale :
    IsIso (moduleUnboundedDerivedBaseChangeMap Λ f g j i h.w) := by
  let e := Functor.mapDerivedCategorySquareIso
    (moduleLowerShriek j Λ) (moduleInverseImage f Λ)
    (moduleInverseImage g Λ) (moduleLowerShriek i Λ)
    (moduleLowerShriekCartesianBaseChangeIso g i j f h Λ).symm
  have hm : (mateEquiv
      (moduleLowerShriekAdjunction j Λ).mapDerivedCategoryAdjunction
      (moduleLowerShriekAdjunction i Λ).mapDerivedCategoryAdjunction
      (TwoSquare.mk _ _ _ _ e.hom)).natTrans =
      (moduleUnboundedDerivedInverseImageSquareIso Λ f g j i h.w).hom :=
    mapDerivedCategorySquareIso_mate
      (moduleLowerShriekAdjunction j Λ) (moduleLowerShriekAdjunction i Λ)
      (moduleLowerShriekCartesianBaseChangeIso g i j f h Λ).symm
      (moduleInverseImageSquareIso Λ f g j i h.w)
      (moduleLowerShriekCartesianBaseChangeIso_inv_mate g i j f h Λ)
  exact isIso_mateEquiv_of_opposite_mate
    (moduleLowerShriekAdjunction j Λ).mapDerivedCategoryAdjunction
    (moduleLowerShriekAdjunction i Λ).mapDerivedCategoryAdjunction
    (moduleUnboundedDerivedAdjunction Λ g) (moduleUnboundedDerivedAdjunction Λ f)
    e (moduleUnboundedDerivedInverseImageSquareIso Λ f g j i h.w).hom hm

end AlgebraicGeometry.Scheme.EtaleCohomology
