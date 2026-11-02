/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleExchangePasting
public import Aglib.CategoryTheory.Functor.CompositionCubeWhole
public import Aglib.CategoryTheory.Functor.SquareTransportPredicate

/-! # The original inverse-image cube for restriction of a square

This is ordinary coefficient-sheaf coherence, independent of derived models,
properness, etaleness and cohomological bounds. All six faces are the original
inverse-image comparisons. Composition coherence, not a desired cube premise,
supplies the result used by unbounded localization.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

variable (Λ : Type (u + 1)) [Ring Λ]

private theorem inverse_square_transport {X S X' S' : Scheme.{u}}
    (f₀ f₁ : X ⟶ S) (f₀' f₁' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h₀ : f₀' ≫ g = g' ≫ f₀) (h₁ : f₁' ≫ g = g' ≫ f₁)
    (a : f₀ = f₁) (b : f₀' = f₁') :
    Functor.ComparisonTransportEquation
      (moduleInverseImageSquareIso Λ f₀ f₀' g g' h₀).symm
      (moduleInverseImageSquareIso Λ f₁ f₁' g g' h₁).symm
      (eqToIso (congrArg (fun k => moduleInverseImage k Λ) a))
      (eqToIso (congrArg (fun k => moduleInverseImage k Λ) b)) :=
  Functor.comparisonTransportEquation_of_squareFamily
    (fun k : X ⟶ S => moduleInverseImage k Λ)
    (fun k : X' ⟶ S' => moduleInverseImage k Λ)
    (moduleInverseImage g Λ) (moduleInverseImage g' Λ)
    (fun k k' => k' ≫ g = g' ≫ k)
    (fun k k' hk => moduleInverseImageSquareIso Λ k k' g g' hk)
    f₀ f₁ f₀' f₁' h₀ h₁ a b

variable {X S X' S' Y T Y' T' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (p : Y ⟶ T) (p' : Y' ⟶ T') (q : T' ⟶ T) (q' : Y' ⟶ Y)
  (jS : T ⟶ S) (jX : Y ⟶ X) (jS' : T' ⟶ S') (jX' : Y' ⟶ X')
  (hf : p ≫ jS = jX ≫ f) (hf' : p' ≫ jS' = jX' ≫ f')
  (hg : q ≫ jS = jS' ≫ g) (hg' : q' ≫ jX = jX' ≫ g')
  (h : f' ≫ g = g' ≫ f) (h' : p' ≫ q = q' ≫ p)

/-- All six original inverse-image faces of a commuting scheme cube satisfy
the actual whole natural-isomorphism cube. -/
theorem moduleInverseImageSquareIso_restriction_cube :
    Functor.ComparisonCubeEquation
      (moduleInverseImageSquareIso Λ f p jS jX hf).symm
      (moduleInverseImageSquareIso Λ f' p' jS' jX' hf').symm
      (moduleInverseImageSquareIso Λ g q jS jS' hg).symm
      (moduleInverseImageSquareIso Λ g' q' jX jX' hg').symm
      (moduleInverseImageSquareIso Λ f f' g g' h)
      (moduleInverseImageSquareIso Λ p p' q q' h') := by
  have h₀ : (p' ≫ q) ≫ jS = jX' ≫ (f' ≫ g) := by
    rw [Category.assoc, hg, ← Category.assoc, hf', Category.assoc]
  have h₁ : (q' ≫ p) ≫ jS = jX' ≫ (g' ≫ f) := by
    rw [Category.assoc, hf, ← Category.assoc, hg', Category.assoc]
  exact Functor.comparisonCubeEquation_of_composition
    (moduleInverseImageSquareIso Λ f p jS jX hf).symm
    (moduleInverseImageSquareIso Λ f' p' jS' jX' hf').symm
    (moduleInverseImageSquareIso Λ g q jS jS' hg).symm
    (moduleInverseImageSquareIso Λ g' q' jX jX' hg').symm
    (moduleInverseImageSquareIso Λ (f' ≫ g) (p' ≫ q) jS jX' h₀).symm
    (moduleInverseImageSquareIso Λ (g' ≫ f) (q' ≫ p) jS jX' h₁).symm
    (moduleInverseImageCompIso Λ g f') (moduleInverseImageCompIso Λ f g')
    (eqToIso (congrArg (fun k => moduleInverseImage k Λ) h))
    (moduleInverseImageCompIso Λ q p') (moduleInverseImageCompIso Λ p q')
    (eqToIso (congrArg (fun k => moduleInverseImage k Λ) h'))
    (moduleInverseImageSquareIso Λ f f' g g' h)
    (moduleInverseImageSquareIso Λ p p' q q' h') rfl rfl
    (moduleInverseImageSquareIso_vComp Λ g f' q p' jS jS' jX' hg hf' h₀)
    (moduleInverseImageSquareIso_vComp Λ f g' p q' jS jX jX' hf hg' h₁)
    (inverse_square_transport Λ (f' ≫ g) (g' ≫ f) (p' ≫ q) (q' ≫ p)
      jS jX' h₀ h₁ h h')

end AlgebraicGeometry.Scheme.EtaleCohomology
