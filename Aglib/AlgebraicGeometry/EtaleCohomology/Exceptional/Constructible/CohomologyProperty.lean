/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.SingleCriterion

/-! # Original constructible and bounded cohomology properties over any ring

These are the same native objects, homology functors and intrinsic bounds.
No finite-ring finiteness theorem is needed to define these properties.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX

/-- Constructibility of the original homology objects in the supplied native D+. -/
def moduleConstructibleCohomologyPlus (X : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)] :
    ObjectProperty (DerivedCategory.Plus (ModuleSheaf X Λ)) :=
  fun K => ∀ i : ℤ, Constructible.Modules.IsConstructible
    ((moduleSheafEquivalence X Λ).inverse.obj
      ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf X Λ) i).obj K))

/-- Bounded constructible objects in the same selected native D+, with no
choice of a complex representative or of cohomological bounds. -/
def moduleBoundedConstructibleCohomologyPlus (X : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)] :
    ObjectProperty (DerivedCategory.Plus (ModuleSheaf X Λ)) :=
  fun K => moduleConstructibleCohomologyPlus X Λ K ∧
    ∃ a b : ℤ, K.IsGE a ∧ K.IsLE b

end AlgebraicGeometry.Scheme.EtaleCohomology
