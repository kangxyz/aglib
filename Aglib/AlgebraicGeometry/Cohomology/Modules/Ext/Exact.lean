/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext
public import Aglib.AlgebraicGeometry.Cohomology.Exact.Modules

/-!
# Original module Ext classes and cohomology connecting maps

The unchanged module-Ext/cohomology comparison carries native Yoneda composition with
an actual short exact extension class to the original additive-sheaf connecting map.
The same identity retains the specified structural-ring linear connecting map, and its
inverse comparison has the corresponding original extension-class formula. No sign,
acyclicity, quasicoherence or finiteness hypothesis is introduced.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (X : Scheme.{u})

/-- The canonical comparison carries the original module extension class to the original
additive cohomology boundary by literal native Yoneda composition. -/
theorem moduleExtCohomologyMap_extClass (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (q : ℕ)
    (x : Ext.{u + 1} (C := X.Modules) (SheafOfModules.unit X.ringCatSheaf) S.X₃ q) :
    moduleExtCohomologyMap X S.X₁ (q + 1) (x.comp hS.extClass rfl) =
      Sheaf.H.δ (moduleCoefficientSequence_shortExact X S hS) q (q + 1) rfl
        (moduleExtCohomologyMap X S.X₃ q x) := by
  rw [moduleExtCohomologyMap_yoneda, Ext.mapExactFunctor_extClass]
  rfl

variable {R : Type u} [CommRing R] (α : R →+* Γ(X, ⊤))

/-- The same original boundary identity retains the existing structural-ring linear map. -/
theorem moduleExtCohomologyMap_connectingOfHom (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (q : ℕ)
    (x : Ext.{u + 1} (C := X.Modules) (SheafOfModules.unit X.ringCatSheaf) S.X₃ q) :
    moduleExtCohomologyMap X S.X₁ (q + 1) (x.comp hS.extClass rfl) =
      moduleCohomologyConnectingOfHom X α S hS q (moduleExtCohomologyMap X S.X₃ q x) :=
  moduleExtCohomologyMap_extClass X S hS q x

/-- The inverse original cohomology comparison sends an actual connecting-map value to
composition with the original module extension class, with positive sign. -/
theorem moduleExtCohomologyAddEquiv_symm_connectingOfHom (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (q : ℕ) (x : Sheaf.H.{u + 1} (moduleAddSheaf X S.X₃) q) :
    (moduleExtCohomologyAddEquiv X S.X₁ (q + 1)).symm
        (moduleCohomologyConnectingOfHom X α S hS q x) =
      ((moduleExtCohomologyAddEquiv X S.X₃ q).symm x).comp hS.extClass rfl := by
  apply (moduleExtCohomologyAddEquiv X S.X₁ (q + 1)).injective
  rw [AddEquiv.apply_symm_apply]
  change moduleCohomologyConnectingOfHom X α S hS q x =
    moduleExtCohomologyMap X S.X₁ (q + 1)
      (((moduleExtCohomologyAddEquiv X S.X₃ q).symm x).comp hS.extClass rfl)
  rw [moduleExtCohomologyMap_connectingOfHom X α S hS q]
  change moduleCohomologyConnectingOfHom X α S hS q x =
    moduleCohomologyConnectingOfHom X α S hS q
      ((moduleExtCohomologyAddEquiv X S.X₃ q) ((moduleExtCohomologyAddEquiv X S.X₃ q).symm x))
  rw [AddEquiv.apply_symm_apply]

end AlgebraicGeometry.Scheme.Cohomology
