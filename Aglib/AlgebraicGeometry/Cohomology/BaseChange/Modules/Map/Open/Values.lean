/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Open

/-! # Values of the original structural-linear open transfer

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

/-- The original restriction map is the original exact Ext transfer on elements. -/
theorem moduleHPrimeRestrictionMap_apply_ext
    {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
    (p : Y ⟶ X) (σ : R →+* S)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
    (h : p.appTop.hom.comp α = β.comp σ)
    {M : X.Modules} {N : Y.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) (n : ℕ)
    (U : X.Opensᵒᵖ) (x : (moduleHPrimePresheaf X α M n).obj U) :
    (moduleHPrimeRestrictionMap p σ α β h φ n).app U x =
      (zariskiPullback p).extCoefficientTransfer
        ((TopCat.Sheaf.openFreeAbelianPullbackIso p.base).inv.app U.unop)
        (moduleCoefficientPullback p φ) n x := rfl

end AlgebraicGeometry.Scheme.Cohomology
