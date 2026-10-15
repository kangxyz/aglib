/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections.Basic
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.PullbackSections
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.BaseChange

/-! # Affine sections with the original structural scalar action

The native affine tilde/section functor is identified with the original module
of top sections. The comparisons preserve the actual section elements and
the structural-ring scalar restrictions.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u}) [IsAffine X]

/-- The affine global-section functor has the original structural scalar action on top sections. -/
theorem affineΓFunctor_smul (M : X.Modules) (a : Γ(X, ⊤))
    (m : (affineΓFunctor X).obj M) :
    a • m = a • (show M.val.obj (op ⊤) from m) := by
  change X.isoSpec.hom.appTop
      ((Spec Γ(X, ⊤)).presheaf.map (𝟙 (op ⊤)) ((Scheme.ΓSpecIso Γ(X, ⊤)).inv a)) •
    (show M.val.obj (op ⊤) from m) = _
  rw [CategoryTheory.Functor.map_id]
  change X.isoSpec.hom.appTop ((Scheme.ΓSpecIso Γ(X, ⊤)).inv a) •
    (show M.val.obj (op ⊤) from m) = _
  simp only [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop, Iso.inv_hom_id_apply]

/-- Actual affine sections identify with native top sections without changing section elements. -/
def affineΓTopSectionsIso (M : X.Modules) :
    (affineΓFunctor X).obj M ≅ M.val.obj (op ⊤) := by
  refine ModuleCat.isoMk (Iso.refl _) ?_
  intro a
  ext m
  exact (affineΓFunctor_smul X M a m).symm

theorem affineΓTopSectionsIso_hom_apply (M : X.Modules) (m : (affineΓFunctor X).obj M) :
    (affineΓTopSectionsIso X M).hom m = m := rfl

theorem affineΓTopSectionsIso_inv_apply (M : X.Modules) (m : M.val.obj (op ⊤)) :
    (affineΓTopSectionsIso X M).inv m = m := rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] (X : Scheme.{u}) (α : A →+* Γ(X, ⊤))

/-- The original structural top-section module is scalar restriction of native affine sections. -/
def moduleAffineTopSectionsIso [IsAffine X] (M : X.Modules) :
    (moduleSectionsPresheaf X α M).obj (op ⊤) ≅
      (ModuleCat.restrictScalars α).obj ((Scheme.Modules.affineΓFunctor X).obj M) :=
  moduleTopSectionsIso X α M ≪≫
    (ModuleCat.restrictScalars α).mapIso (Scheme.Modules.affineΓTopSectionsIso X M).symm

theorem moduleAffineTopSectionsIso_hom_apply [IsAffine X] (M : X.Modules)
    (m : (moduleSectionsPresheaf X α M).obj (op ⊤)) :
    (moduleAffineTopSectionsIso X α M).hom m = m := rfl

theorem moduleAffineTopSectionsIso_inv_apply [IsAffine X] (M : X.Modules)
    (m : (ModuleCat.restrictScalars α).obj ((Scheme.Modules.affineΓFunctor X).obj M)) :
    (moduleAffineTopSectionsIso X α M).inv m = m := rfl

end AlgebraicGeometry.Scheme.Cohomology
