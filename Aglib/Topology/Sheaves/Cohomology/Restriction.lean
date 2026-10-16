/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.ExtensionByZero.Free
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Abelian

/-!
# The actual open cohomology under restriction

Exact extension by zero and the native Ext adjunction identify the existing
open cohomology of an abelian sheaf with the existing open cohomology of its
restriction. The equivalence retains the original free-open comparison and
the actual extension-by-zero adjunction unit. It is natural in coefficients.
No geometric acyclicity, finiteness or supplied cohomological comparison is
assumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite

namespace TopCat.Sheaf

universe u

variable {X : TopCat.{u}} (U : Opens X)

local instance :
    HasExt.{u + 1} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

local instance :
    HasExt.{u + 1} (CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}) :=
  HasExt.standard _

local instance : (U.sheafRestrict (C := AddCommGrpCat.{u})).IsRightAdjoint :=
  (extensionByZeroRestrictAdjunction U).isRightAdjoint

local instance : (U.sheafRestrict (C := AddCommGrpCat.{u})).Additive where
  map_add := by intros; rfl

/-- Native open-Ext cohomology of a restricted sheaf, through exact extension by zero. -/
def cohomologyOpenRestrictionAddEquiv
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (n : ℕ) (V : Opens U) :
    CategoryTheory.Sheaf.H'.{u + 1} F n (U.isOpenEmbedding.functor.obj V) ≃+
      CategoryTheory.Sheaf.H'.{u + 1}
        ((U.sheafRestrict (C := AddCommGrpCat.{u})).obj F) n V := by
  let e := ((extFunctor.{u + 1} n).mapIso
    (openFreeAbelianExtensionByZeroObjIso U V).op).app F
  exact e.addCommGroupIsoToAddEquiv.trans (extensionByZeroRestrictAdjunction U).extEquiv


/-- The original restriction equivalence has the original adjunction-unit formula on Ext. -/
theorem cohomologyOpenRestrictionAddEquiv_apply
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (n : ℕ) (V : Opens U)
    (x : CategoryTheory.Sheaf.H'.{u + 1} F n (U.isOpenEmbedding.functor.obj V)) :
    cohomologyOpenRestrictionAddEquiv U F n V x =
      (Ext.mk₀ ((extensionByZeroRestrictAdjunction U).unit.app
          ((openFreeAbelianFunctor (TopCat.of U)).obj V) ≫
        (U.sheafRestrict (C := AddCommGrpCat.{u})).map
          (openFreeAbelianExtensionByZeroObjIso U V).hom)).comp
        (x.mapExactFunctor (U.sheafRestrict (C := AddCommGrpCat.{u}))) (Nat.zero_add n) := by
  change (Ext.mk₀ ((extensionByZeroRestrictAdjunction U).unit.app
      ((openFreeAbelianFunctor (TopCat.of U)).obj V))).comp
      (((Ext.mk₀ (openFreeAbelianExtensionByZeroObjIso U V).hom).comp x
        (Nat.zero_add n)).mapExactFunctor (U.sheafRestrict (C := AddCommGrpCat.{u})))
      (Nat.zero_add n) = _
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc _ _ _ (Nat.zero_add 0) (by lia) (by lia), Ext.mk₀_comp_mk₀]

/-- The actual restriction equivalence is natural in the abelian coefficient sheaf. -/
theorem cohomologyOpenRestrictionAddEquiv_naturality
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (φ : F ⟶ G) (n : ℕ) (V : Opens U)
    (x : CategoryTheory.Sheaf.H'.{u + 1} F n (U.isOpenEmbedding.functor.obj V)) :
    cohomologyOpenRestrictionAddEquiv U G n V
        (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X) n).map φ).app
            (op (U.isOpenEmbedding.functor.obj V)) x) =
      ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology U) n).map
          ((U.sheafRestrict (C := AddCommGrpCat.{u})).map φ)).app (op V)
            (cohomologyOpenRestrictionAddEquiv U F n V x) := by
  rw [cohomologyOpenRestrictionAddEquiv_apply, cohomologyOpenRestrictionAddEquiv_apply]
  change (Ext.mk₀ _).comp
      ((x.comp (Ext.mk₀ φ) (Nat.add_zero n)).mapExactFunctor
        (U.sheafRestrict (C := AddCommGrpCat.{u}))) (Nat.zero_add n) =
    ((Ext.mk₀ _).comp (x.mapExactFunctor (U.sheafRestrict (C := AddCommGrpCat.{u})))
      (Nat.zero_add n)).comp
        (Ext.mk₀ ((U.sheafRestrict (C := AddCommGrpCat.{u})).map φ)) (Nat.add_zero n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc _ _ _ (Nat.zero_add n) (Nat.add_zero n) (by lia)]

end TopCat.Sheaf
