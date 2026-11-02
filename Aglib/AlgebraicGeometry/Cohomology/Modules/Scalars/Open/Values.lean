/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars.Open
public import Aglib.Topology.Sheaves.FreeAbelianPullback

/-! # Values of the original structural-linear index map

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

/-- The native index map is original degree-zero source precomposition. -/
theorem moduleHPrimePresheaf_map_apply_ext
    (X : Scheme.{u}) {R : Type u} [CommRing R] (α : R →+* Γ(X, ⊤))
    (M : X.Modules) (n : ℕ) {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (x : (moduleHPrimePresheaf X α M n).obj U) :
    letI : HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}) :=
      structureSheafHasExt X
    (moduleHPrimePresheaf X α M n).map i x =
      (Ext.mk₀.{u + 1} ((TopCat.Sheaf.openFreeAbelianFunctor X.toTopCat).map i.unop)).comp x
        (Nat.zero_add n) := rfl

end AlgebraicGeometry.Scheme.Cohomology
