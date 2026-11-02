/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.Scalars

/-! # Values of the original structural-linear top comparison

These value laws retain the original constructors and Ext classes.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Cohomology
universe u

/-- The original top comparison acts by its original source isomorphism. -/
theorem moduleHPrimeTopLinearEquivOfHom_apply_ext
    (X : Scheme.{u}) {R : Type u} [CommRing R] (α : R →+* Γ(X, ⊤))
    (M : X.Modules) (n : ℕ) (x : Sheaf.H'.{u + 1} (moduleAddSheaf X M) n ⊤) :
    letI := moduleHPrimeModuleOfHom X α M n ⊤
    letI := moduleCohomologyModuleOfHom X α M n
    moduleHPrimeTopLinearEquivOfHom X α M n x =
      (Ext.mk₀ (additiveOpenTopIsoInteger X).inv).comp x (Nat.zero_add n) := rfl

end AlgebraicGeometry.Scheme.Cohomology
