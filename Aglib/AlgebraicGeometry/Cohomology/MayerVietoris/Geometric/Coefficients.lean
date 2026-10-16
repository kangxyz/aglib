/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.Geometric

/-! # Coefficient naturality of the native geometric open-cohomology map

The original inverse-image map on the native open-Ext presheaf respects
every actual commuting coefficient square. This supplies the structural
scalar comparison for the original tensor mate on open cohomology.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

/-- The original geometric open-cohomology transformation respects an actual coefficient square. -/
theorem zariskiCohomologyOpenMap_coefficients
    {A A' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {B B' : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    (a : (zariskiPullback p).obj A ⟶ B) (a' : (zariskiPullback p).obj A' ⟶ B')
    (f : A ⟶ A') (g : B ⟶ B') (h : (zariskiPullback p).map f ≫ a' = a ≫ g) (n : ℕ) :
    (Sheaf.cohomologyPresheafFunctor.{u + 1} (Opens.grothendieckTopology X) n).map f ≫
        zariskiCohomologyOpenMap p A' B' a' n =
      zariskiCohomologyOpenMap p A B a n ≫
        Functor.whiskerLeft (Opens.map p.base).op
          ((Sheaf.cohomologyPresheafFunctor.{u + 1}
            (Opens.grothendieckTopology Y) n).map g) := by
  ext U x
  change Ext.{u + 1} ((additiveOpenFreeFunctor X).obj U.unop) A n at x
  change ((Ext.mk₀ ((additiveOpenPullbackIso p).inv.app U.unop)).comp
      ((x.comp (Ext.mk₀ f) (Nat.add_zero n)).mapExactFunctor (zariskiPullback p))
      (Nat.zero_add n)).comp (Ext.mk₀ a') (Nat.add_zero n) =
    (((Ext.mk₀ ((additiveOpenPullbackIso p).inv.app U.unop)).comp
      (x.mapExactFunctor (zariskiPullback p)) (Nat.zero_add n)).comp
      (Ext.mk₀ a) (Nat.add_zero n)).comp (Ext.mk₀ g) (Nat.add_zero n)
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, h]

end AlgebraicGeometry.Scheme.Cohomology
