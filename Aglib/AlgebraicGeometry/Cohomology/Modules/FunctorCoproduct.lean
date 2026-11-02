/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Functor
public import Mathlib.Algebra.DirectSum.Module

/-! # Original cohomology carriers of a complete coproduct comparison

This changes only the presentation of a supplied linear equivalence. Both
sides retain the original `Sheaf.H` and its specified structural-ring action.
The independent target module is kept abstract until the entire carrier
comparison has been constructed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace DirectSum

universe u v

namespace AlgebraicGeometry.Scheme.Cohomology

variable (X : Scheme.{u}) {R : Type u} [CommRing R]
  (α : R →+* Γ(X, ⊤)) (q : ℕ) {δ : Type v} [DecidableEq δ]

/-- A whole equivalence on the actual cohomology functor values, expressed on
its literal original sheaf-cohomology carriers. No coproduct or model is chosen. -/
def moduleCohomologyFunctorCoproductCarrierEquiv (M : δ → X.Modules) (N : X.Modules)
    (e : (⨁ i, (moduleCohomologyFunctorOfHom X α q).obj (M i)) ≃ₗ[R]
      (moduleCohomologyFunctorOfHom X α q).obj N) :
    letI : ∀ i, Module R (Sheaf.H.{u + 1} (moduleAddSheaf X (M i)) q) :=
      fun i => moduleCohomologyModuleOfHom X α (M i) q
    letI := moduleCohomologyModuleOfHom X α N q
    (⨁ i, Sheaf.H.{u + 1} (moduleAddSheaf X (M i)) q) ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X N) q := e

end AlgebraicGeometry.Scheme.Cohomology
