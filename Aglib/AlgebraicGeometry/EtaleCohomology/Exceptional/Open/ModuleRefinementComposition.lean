/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.ComparisonCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleRefinementCoherence
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleRefinementExchangeCoherence

/-! # Identity and composition for the existing Cartesian refinement comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

/-- The original refinement comparison is conjugate to the adjusted original
right exchange, rather than to a newly chosen left-adjoint isomorphism. -/
theorem conjugateEquiv_moduleLowerShriekCartesianIdentityIso_hom
    {U Y X : Scheme.{u}} (i : U ⟶ Y) (j : U ⟶ X) (f : Y ⟶ X)
    [Etale i] [Etale j] (h : IsPullback (𝟙 U) i j f)
    (Λ : Type (u + 1)) [Ring Λ] :
    conjugateEquiv (moduleLowerShriekAdjunction i Λ)
      ((moduleLowerShriekAdjunction j Λ).comp (moduleInverseImageAdjunction f Λ))
      (moduleLowerShriekCartesianIdentityIso i j f h Λ).hom =
        (moduleRefinementExchangeIso i j f h Λ).inv :=
  conjugateEquiv_normalizedComparison
    ((moduleLowerShriekAdjunction j Λ).comp (moduleInverseImageAdjunction f Λ))
    (moduleLowerShriekAdjunction i Λ) (moduleInverseImageAdjunction (𝟙 U) Λ)
    (moduleLowerShriekCartesianBaseChangeIso (𝟙 U) i j f h Λ)
    (moduleCartesianExchangeIso (𝟙 U) i j f h Λ)
    (moduleInverseImageIdIso Λ U) (moduleDirectImageIdIso Λ U)
    (conjugateEquiv_moduleLowerShriekCartesianBaseChangeIso_hom (𝟙 U) i j f h Λ)
    (conjugateEquiv_moduleInverseImageIdIso_hom Λ U)

/-- Composition of the existing native Cartesian refinement comparisons. -/
theorem moduleLowerShriekCartesianIdentityIso_comp
    {U Z Y X : Scheme.{u}} (i : U ⟶ Z) (j : U ⟶ Y) (l : U ⟶ X)
    (f : Y ⟶ X) (k : Z ⟶ Y) [Etale i] [Etale j] [Etale l]
    (hf : IsPullback (𝟙 U) j l f) (hk : IsPullback (𝟙 U) i j k)
    (h : IsPullback (𝟙 U) i l (k ≫ f)) (Λ : Type (u + 1)) [Ring Λ] :
    moduleLowerShriekCartesianIdentityIso i l (k ≫ f) h Λ =
      Functor.isoWhiskerLeft (moduleLowerShriek l Λ) (moduleInverseImageCompIso Λ f k) ≪≫
        (Functor.associator (moduleLowerShriek l Λ)
          (moduleInverseImage f Λ) (moduleInverseImage k Λ)).symm ≪≫
        Functor.isoWhiskerRight (moduleLowerShriekCartesianIdentityIso j l f hf Λ)
          (moduleInverseImage k Λ) ≪≫
        moduleLowerShriekCartesianIdentityIso i j k hk Λ :=
  adjunctionComparison_comp_of_conjugate
    (moduleLowerShriekAdjunction i Λ) (moduleLowerShriekAdjunction j Λ)
    (moduleLowerShriekAdjunction l Λ) (moduleInverseImageAdjunction f Λ)
    (moduleInverseImageAdjunction k Λ) (moduleInverseImageAdjunction (k ≫ f) Λ)
    (moduleLowerShriekCartesianIdentityIso j l f hf Λ)
    (moduleLowerShriekCartesianIdentityIso i j k hk Λ)
    (moduleLowerShriekCartesianIdentityIso i l (k ≫ f) h Λ)
    (moduleRefinementExchangeIso j l f hf Λ) (moduleRefinementExchangeIso i j k hk Λ)
    (moduleRefinementExchangeIso i l (k ≫ f) h Λ)
    (moduleInverseImageCompIso Λ f k) (moduleDirectImageCompIso Λ f k)
    (conjugateEquiv_moduleLowerShriekCartesianIdentityIso_hom j l f hf Λ)
    (conjugateEquiv_moduleLowerShriekCartesianIdentityIso_hom i j k hk Λ)
    (conjugateEquiv_moduleLowerShriekCartesianIdentityIso_hom i l (k ≫ f) h Λ)
    (conjugateEquiv_moduleInverseImageCompIso_hom Λ f k)
    (moduleRefinementExchangeIso_comp i j l f k hf hk h Λ)

/-- Identity normalization of the existing native Cartesian refinement comparison. -/
theorem moduleLowerShriekCartesianIdentityIso_id
    {U X : Scheme.{u}} (i : U ⟶ X) [Etale i]
    (h : IsPullback (𝟙 U) i i (𝟙 X)) (Λ : Type (u + 1)) [Ring Λ] :
    moduleLowerShriekCartesianIdentityIso i i (𝟙 X) h Λ =
      Functor.isoWhiskerLeft (moduleLowerShriek i Λ) (moduleInverseImageIdIso Λ X) ≪≫
        Functor.rightUnitor (moduleLowerShriek i Λ) :=
  adjunctionComparison_id_of_conjugate
    (moduleLowerShriekAdjunction i Λ) (moduleInverseImageAdjunction (𝟙 X) Λ)
    (moduleLowerShriekCartesianIdentityIso i i (𝟙 X) h Λ)
    (moduleRefinementExchangeIso i i (𝟙 X) h Λ)
    (moduleInverseImageIdIso Λ X) (moduleDirectImageIdIso Λ X)
    (conjugateEquiv_moduleLowerShriekCartesianIdentityIso_hom i i (𝟙 X) h Λ)
    (conjugateEquiv_moduleInverseImageIdIso_hom Λ X)
    (moduleRefinementExchangeIso_id i h Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
