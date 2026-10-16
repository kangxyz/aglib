/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Actual module sections over a specified structural ring

The native module presheaf is restricted through a ring map to global
functions. Its value at the whole space agrees with the original top-section
module under scalar restriction, by the literal identity on elements.

These object-level comparisons require no cohomology, quasicoherence,
affineness or base-change theorem. Cech computations and geometric section
base change share this single implementation.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {A : Type u} [CommRing A] (X : Scheme.{u}) (α : A →+* Γ(X, ⊤))

/-- Actual module sections as modules over the specified structural ring. -/
def moduleSectionsPresheaf (M : X.Modules) : X.Opensᵒᵖ ⥤ ModuleCat.{u} A :=
  (PresheafOfModules.forgetToPresheafModuleCat (op ⊤)
    (isTerminalTop (α := X.Opens)).op).obj M.val ⋙ ModuleCat.restrictScalars α

/-- The native structural section presheaf at the top is the original scalar restriction. -/
def moduleTopSectionsIso (M : X.Modules) :
    (moduleSectionsPresheaf X α M).obj (op ⊤) ≅
      (ModuleCat.restrictScalars α).obj (M.val.obj (op ⊤)) := by
  let φ := (X.ringCatSheaf.obj.map (𝟙 (op ⊤))).hom
  have hφ : φ = RingHom.id Γ(X, ⊤) := by
    dsimp [φ]
    rw [CategoryTheory.Functor.map_id]
    rfl
  exact (ModuleCat.restrictScalars α).mapIso
    (ModuleCat.restrictScalarsId'App φ hφ (M.val.obj (op ⊤)))

theorem moduleTopSectionsIso_hom_apply (M : X.Modules)
    (m : (moduleSectionsPresheaf X α M).obj (op ⊤)) :
    (moduleTopSectionsIso X α M).hom m = m := rfl

theorem moduleTopSectionsIso_inv_apply (M : X.Modules)
    (m : (ModuleCat.restrictScalars α).obj (M.val.obj (op ⊤))) :
    (moduleTopSectionsIso X α M).inv m = m := rfl

/-- The original structural section presheaf, functorially in its module coefficient. -/
def moduleSectionsPresheafFunctor {A : Type u} [CommRing A]
    (X : Scheme.{u}) (α : A →+* Γ(X, ⊤)) :
    X.Modules ⥤ (X.Opensᵒᵖ ⥤ ModuleCat.{u} A) where
  obj M := moduleSectionsPresheaf X α M
  map φ := Functor.whiskerRight
    ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤)
      (isTerminalTop (α := X.Opens)).op).map φ.val) (ModuleCat.restrictScalars α)
  map_id M := by
    ext U x
    rfl
  map_comp φ ψ := by
    ext U x
    rfl

instance moduleSectionsPresheafFunctor_additive :
    (moduleSectionsPresheafFunctor X α).Additive where
  map_add := by
    intros
    ext U x
    rfl

theorem moduleSectionsPresheafFunctor_obj {A : Type u} [CommRing A]
    (X : Scheme.{u}) (α : A →+* Γ(X, ⊤)) (M : X.Modules) :
    (moduleSectionsPresheafFunctor X α).obj M = moduleSectionsPresheaf X α M := rfl

theorem moduleSectionsPresheafFunctor_map_apply {A : Type u} [CommRing A]
    (X : Scheme.{u}) (α : A →+* Γ(X, ⊤)) {M N : X.Modules} (φ : M ⟶ N)
    (U : X.Opensᵒᵖ) (m : (moduleSectionsPresheaf X α M).obj U) :
    ((moduleSectionsPresheafFunctor X α).map φ).app U m = φ.app U.unop m := rfl

end AlgebraicGeometry.Scheme.Cohomology
