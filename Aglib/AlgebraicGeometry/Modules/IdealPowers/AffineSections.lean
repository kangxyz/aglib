/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.AffineEvaluation
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.Multiplication
public import Aglib.AlgebraicGeometry.Modules.Locality.Sections
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Sections
public import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Actual affine ideal-power section equivalences over the structural ring -/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable (X : Scheme.{u}) {A : Type u} [CommRing A] (α : A →+* Γ(X, ⊤))

/-- The specified structural ring map on an open. -/
def idealSectionRingHom (U : X.Opens) : A →+* Γ(X, U) :=
  ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom).comp α

/-- The original section module with its specified structural scalar action. -/
abbrev idealSectionModule (F : X.Modules) (U : X.Opens) : Module A (Γ(F, U)) :=
  inferInstanceAs (Module A ((Cohomology.moduleSectionsPresheaf X α F).obj (op U)))

/-- The original section map, linear over the structural ring. -/
def idealSectionMap {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens) :
    letI := idealSectionModule X α F U
    letI := idealSectionModule X α G U
    Γ(F, U) →ₗ[A] Γ(G, U) := by
  letI := idealSectionModule X α F U
  letI := idealSectionModule X α G U
  exact ((Cohomology.moduleSectionsPresheafFunctor X α).map φ).app (op U) |>.hom

variable (F : X.Modules) [F.IsQuasicoherent]

/-- The native structural-ring ideal multiple is the affine section image of the ideal sheaf. -/
theorem idealMultiple_affine_range_structural (J : Ideal A) (U : X.affineOpens) :
    letI := idealSectionModule X α F U.val
    letI := idealSectionModule X α (idealMultiple X α F J) U.val
    (idealSectionMap X α (idealMultipleι X α F J) U.val).range =
      J • (⊤ : Submodule A (Γ(F, U.val))) := by
  let := idealSectionModule X α F U.val
  let := idealSectionModule X α (idealMultiple X α F J) U.val
  let : Algebra A Γ(X, U.val) := (idealSectionRingHom X α U.val).toAlgebra
  let : IsScalarTower A Γ(X, U.val) (Γ(F, U.val)) :=
    IsScalarTower.of_compHom A Γ(X, U.val) (Γ(F, U.val))
  have h := congrArg (fun N : Submodule Γ(X, U.val) (Γ(F, U.val)) => N.restrictScalars A)
    (idealMultiple_affine_range X α F J U)
  rw [idealSectionSpan_eq_smul] at h
  exact h.trans (Submodule.restrictScalars_map_smul_eq J ⊤)

/-- The actual affine sections of an ideal multiple identify with the native ideal multiple.
The forward map is the original coefficient inclusion, not an unrelated equivalence. -/
def idealMultipleAffineSectionsEquiv (J : Ideal A) (U : X.affineOpens) :
    letI := idealSectionModule X α F U.val
    letI := idealSectionModule X α (idealMultiple X α F J) U.val
    Γ(idealMultiple X α F J, U.val) ≃ₗ[A] ↥(J • (⊤ : Submodule A (Γ(F, U.val)))) := by
  letI := idealSectionModule X α F U.val
  letI := idealSectionModule X α (idealMultiple X α F J) U.val
  exact (LinearEquiv.ofInjective (idealSectionMap X α (idealMultipleι X α F J) U.val)
    (moduleHom_app_injective (idealMultipleι X α F J) U.val)).trans
      (LinearEquiv.ofEq _ _ (idealMultiple_affine_range_structural X α F J U))

/-- The affine identification retains the original section inclusion literally. -/
theorem idealMultipleAffineSectionsEquiv_apply (J : Ideal A) (U : X.affineOpens)
    (x : Γ(idealMultiple X α F J, U.val)) :
    (idealMultipleAffineSectionsEquiv X α F J U x).val =
      (idealMultipleι X α F J).app U.val x := rfl

/-- Ideal-inclusion transitions become the literal inclusions of affine ideal multiples. -/
theorem idealMultipleAffineSectionsEquiv_map {J K : Ideal A} (h : J ≤ K)
    (U : X.affineOpens) (x : Γ(idealMultiple X α F J, U.val)) :
    (idealMultipleAffineSectionsEquiv X α F K U
      ((idealMultipleMap X α F h).app U.val x)).val =
        (idealMultipleAffineSectionsEquiv X α F J U x).val := by
  exact congrArg (fun k => k.app U.val x) (idealMultipleMap_ι X α F h)

/-- Homogeneous multiplication becomes the original structural scalar multiplication. -/
theorem idealMultipleAffineSectionsEquiv_mul {J K : Ideal A} (a : A)
    (ha : ∀ b ∈ J, a * b ∈ K) (U : X.affineOpens)
    (x : Γ(idealMultiple X α F J, U.val)) :
    (idealMultipleAffineSectionsEquiv X α F K U
      ((idealMultipleMul X α F a ha).app U.val x)).val =
        idealSectionRingHom X α U.val a •
          (idealMultipleAffineSectionsEquiv X α F J U x).val := by
  have h := congrArg (fun k => k.app U.val x) (idealMultipleMul_ι X α F a ha)
  exact h.trans (globalScalarEndomorphism_app X F (α a) U.val _)

/-- Affine restriction is preserved by the original-image section identification. -/
theorem idealMultipleAffineSectionsEquiv_restrict (J : Ideal A)
    (U V : X.affineOpens) (i : U.val ⟶ V.val)
    (x : Γ(idealMultiple X α F J, V.val)) :
    (idealMultipleAffineSectionsEquiv X α F J U
      ((idealMultiple X α F J).val.map i.op x)).val =
        F.val.map i.op (idealMultipleAffineSectionsEquiv X α F J V x).val := by
  exact PresheafOfModules.naturality_apply (idealMultipleι X α F J).val i.op x

end AlgebraicGeometry.Scheme.Modules
