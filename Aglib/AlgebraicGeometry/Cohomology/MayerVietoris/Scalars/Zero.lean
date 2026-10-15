/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.Scalars

/-! # The original degree-zero Mayer–Vietoris restriction is monomorphic

The original free-open Mayer–Vietoris epimorphism gives injectivity after
degree-zero Ext. Faithful scalar forgetting transfers this to the same
native restriction map with its structural module action.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CategoryTheory.Abelian

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

namespace AlgebraicGeometry.Scheme.Cohomology

private theorem mayerVietorisToBiprod_mono_zero (X : Scheme.{u}) (U V : X.Opens)
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    Mono ((Opens.mayerVietorisSquare U V).toBiprod A 0) := by
  let S := Opens.mayerVietorisSquare U V
  let : Epi S.shortComplex.g := S.shortComplex_shortExact.epi_g
  apply (AddCommGrpCat.mono_iff_injective _).mpr
  intro x y hxy
  apply Ext.precomp_mk₀_injective_of_epi A S.shortComplex.g
  change (Ext.mk₀ S.shortComplex.g).comp x (Nat.zero_add 0) =
    (Ext.mk₀ S.shortComplex.g).comp y (Nat.zero_add 0)
  erw [← S.biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply A x,
    ← S.biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply A y, hxy]

/-- The original degree-zero sum of restriction maps is monomorphic with its actual scalars. -/
theorem moduleMayerVietorisToBiprod_mono_zero (X : Scheme.{u}) {R : Type u} [CommRing R]
    (α : R →+* Γ(X, ⊤)) (M : X.Modules) (U V : X.Opens) :
    Mono (moduleMayerVietorisToBiprod X α M U V 0) := by
  let G := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  let P := moduleHPrimePresheaf X α M 0
  have h : G.map (moduleMayerVietorisToBiprod X α M U V 0) ≫
      (G.mapBiprod (P.obj (op U)) (P.obj (op V))).hom =
    (Opens.mayerVietorisSquare U V).toBiprod (moduleAddSheaf X M) 0 := by
    exact biprod.map_lift_mapBiprod G _ _ _ _
  let : Mono ((Opens.mayerVietorisSquare U V).toBiprod (moduleAddSheaf X M) 0) :=
    mayerVietorisToBiprod_mono_zero X U V (moduleAddSheaf X M)
  exact G.mono_of_mono_map (mono_of_mono_fac h)

end AlgebraicGeometry.Scheme.Cohomology
