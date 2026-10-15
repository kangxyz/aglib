/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
/-!
# Global-section multiplication on the structure module sheaf

Original global sections act on the actual unit module sheaf by their restrictions.
This action preserves products and units and commutes with the canonical open
restriction isomorphisms. Invertible sections give actual sheaf automorphisms.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- A genuine global section, with its original restrictions on every open. -/
def unitGlobalSection (X : Scheme.{u}) (s : Γ(X, ⊤)) :
    (SheafOfModules.unit X.ringCatSheaf).sections :=
  _root_.PresheafOfModules.sectionsMk (fun U =>
    (X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom s) (by
      intro U V f
      change (X.presheaf.map f).hom
        ((X.presheaf.map (homOfLE le_top).op).hom s) = _
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl)

/-- Multiplication by a global section as an endomorphism of the structure module sheaf. -/
def unitMul (X : Scheme.{u}) (s : Γ(X, ⊤)) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm (unitGlobalSection X s)

/-- Multiplication is computed by the original restricted scalar on each open. -/
lemma unitMul_app (X : Scheme.{u}) (s : Γ(X, ⊤)) (U : X.Opens)
    (x : Γ(X, U)) :
    Scheme.Modules.Hom.app (unitMul X s) U x = x * (X.presheaf.map (homOfLE le_top).op).hom s := rfl

lemma unitMul_one (X : Scheme.{u}) : unitMul X 1 = 𝟙 _ := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change Γ(X, U) at x
  change x * (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom 1 = x
  simp

lemma unitMul_mul (X : Scheme.{u}) (s t : Γ(X, ⊤)) :
    unitMul X (s * t) = unitMul X s ≫ unitMul X t := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change Γ(X, U) at x
  change x * (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom (s * t) =
    (x * (X.presheaf.map (homOfLE le_top).op).hom s) *
      (X.presheaf.map (homOfLE le_top).op).hom t
  simp [mul_assoc]

/-- The original open-restriction unit isomorphism intertwines scalar multiplication. -/
lemma unitMul_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (s : Γ(Y, ⊤)) :
    (Scheme.Modules.restrictFunctor f).map (unitMul Y s) ≫
      (Scheme.Modules.restrictUnitIso f).hom =
    (Scheme.Modules.restrictUnitIso f).hom ≫ unitMul X (f.appTop.hom s) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change Γ(Y, f ''ᵁ U) at x
  change (f.appIso U).hom.hom
    (x * (Y.presheaf.map (homOfLE le_top).op).hom s) =
    (f.appIso U).hom.hom x * (X.presheaf.map (homOfLE le_top).op).hom (f.appTop.hom s)
  rw [map_mul]
  congr 1
  have h : Y.presheaf.map (homOfLE (show f ''ᵁ U ≤ ⊤ from le_top)).op ≫
      (f.appIso U).hom = f.appTop ≫ X.presheaf.map (homOfLE le_top).op := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  exact congrArg (fun k => CommRingCat.Hom.hom k s) h

/-- An invertible global section gives an automorphism of the actual unit sheaf. -/
def unitMulIso (X : Scheme.{u}) (s : (Γ(X, ⊤))ˣ) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅ SheafOfModules.unit X.ringCatSheaf where
  hom := unitMul X s
  inv := unitMul X (↑s⁻¹)
  hom_inv_id := by rw [← unitMul_mul]; simpa using unitMul_one X
  inv_hom_id := by rw [← unitMul_mul]; simpa using unitMul_one X

end AlgebraicGeometry.Scheme.Modules
