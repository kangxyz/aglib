/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.BidualAffine
public import Aglib.AlgebraicGeometry.Modules.InternalHom.LocallyFree
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Sections
public import Aglib.AlgebraicGeometry.Modules.Locality.AffineIsomorphisms
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Canonical biduality for finite locally free modules

The original affine evaluation comparison and finite projectivity prove that
canonical evaluation is invertible. No rank-one or Noetherian hypothesis is
used, and neither the dual sheaf nor the evaluation map is reconstructed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

variable {X : Scheme.{u}} (M : X.Modules) [IsFiniteLocallyFree X M]

/-- Original bidual evaluation is invertible on every actual affine restriction. -/
theorem bidualMap_restrict_isIso_of_finiteLocallyFree {R : CommRingCat.{u}}
    (j : Spec R ⟶ X) [IsOpenImmersion j] :
    IsIso ((restrictFunctor j).map (bidualMap X M)) := by
  let : IsFiniteLocallyFree X (dualSheaf X M) := InternalHom.finiteLocallyFree_dual M
  let : IsFiniteLocallyFree X (dualSheaf X (dualSheaf X M)) :=
    InternalHom.finiteLocallyFree_dual (dualSheaf X M)
  let P := moduleSpecΓFunctor.obj (M.restrict j)
  let : Module.Finite R P := finite_globalSections_of_finiteLocallyFree R (M.restrict j)
  let : Module.Projective R P :=
    projective_globalSections_of_finiteLocallyFree R (M.restrict j)
  let f := moduleSpecΓFunctor.map ((restrictFunctor j).map (bidualMap X M))
  let e := affineBidualSectionsEquiv j M
  have he : (fun m => e (f m)) = Module.Dual.eval R P := by
    funext m
    exact affineBidualSectionsEquiv_evaluation j M m
  have hf : Function.Bijective f := by
    have h := Module.bijective_dual_eval R P
    rw [← he] at h
    exact (e.bijective.of_comp_iff' f).mp h
  let : IsIso f := (ConcreteCategory.isIso_iff_bijective f).mpr hf
  exact isIso_of_globalSections_isIso ((restrictFunctor j).map (bidualMap X M))

/-- The existing canonical evaluation is an isomorphism for every vector bundle. -/
theorem bidualMap_isIso_of_finiteLocallyFree : IsIso (bidualMap X M) := by
  exact isIso_of_affineRestrictions (bidualMap X M)
    (fun _ j _ => bidualMap_restrict_isIso_of_finiteLocallyFree M j)

/-- Canonical biduality keeps the original evaluation as its forward map. -/
def finiteLocallyFreeBidualIso : M ≅ dualSheaf X (dualSheaf X M) := by
  let := bidualMap_isIso_of_finiteLocallyFree M
  exact asIso (bidualMap X M)

@[simp] theorem finiteLocallyFreeBidualIso_hom :
    (finiteLocallyFreeBidualIso M).hom = bidualMap X M := rfl

end AlgebraicGeometry.Scheme.Modules.Invertible
