/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
/-! # The original scalar-extension unit over a coefficient ring

Restriction along compatible coefficient maps retains the literal adjunction unit and
its unit-pure-tensor formula. The scalar map remains an explicit ring homomorphism.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped TensorProduct Matrix ChangeOfRings
universe u v
namespace ModuleCat
variable {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
variable (a : R →+* A) (φ : A →+* S) (c : R →+* S) (h : c = φ.comp a)

/-- The original extension/restriction adjunction unit over a compatible coefficient ring. -/
def restrictedExtensionUnit (M : ModuleCat.{u} A) :
    (restrictScalars a).obj M ⟶ (restrictScalars c).obj ((extendScalars φ).obj M) :=
  (restrictScalars a).map ((extendRestrictScalarsAdj φ).unit.app M) ≫
    (restrictScalarsComp'App a φ c h ((extendScalars φ).obj M)).inv

/-- The restricted original unit is the literal unit pure tensor for the specified ring map. -/
theorem restrictedExtensionUnit_apply (M : ModuleCat.{u} A) (x : (restrictScalars a).obj M) :
    restrictedExtensionUnit a φ c h M x = (1 : S) ⊗ₜ[A,φ] (x : M) := rfl

end ModuleCat
