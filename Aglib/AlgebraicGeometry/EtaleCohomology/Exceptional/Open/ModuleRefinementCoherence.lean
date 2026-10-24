/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleCartesianBaseChange
public import Aglib.CategoryTheory.Adjunction.LeftAdjointComparison

/-! # Original adjunction normalization of the Cartesian refinement comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable {V U Y X : Scheme.{u}} (g : V ⟶ U) (i : V ⟶ Y) (j : U ⟶ X) (f : Y ⟶ X)
  [Etale i] [Etale j] (h : IsPullback g i j f) (Λ : Type (u + 1)) [Ring Λ]

/-- The existing Cartesian lower-shriek comparison is conjugate to the inverse of
its existing right-adjoint exchange, with the original native adjunctions. -/
theorem conjugateEquiv_moduleLowerShriekCartesianBaseChangeIso_hom :
    conjugateEquiv
      ((moduleInverseImageAdjunction g Λ).comp (moduleLowerShriekAdjunction i Λ))
      ((moduleLowerShriekAdjunction j Λ).comp (moduleInverseImageAdjunction f Λ))
      (moduleLowerShriekCartesianBaseChangeIso g i j f h Λ).hom =
        (moduleCartesianExchangeIso g i j f h Λ).inv :=
  conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
    ((moduleLowerShriekAdjunction j Λ).comp (moduleInverseImageAdjunction f Λ))
    ((moduleInverseImageAdjunction g Λ).comp (moduleLowerShriekAdjunction i Λ))
    (moduleCartesianExchangeIso g i j f h Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
