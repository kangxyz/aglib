/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.RingTheory.FiniteLength.TensorInjectivity
import Mathlib.Algebra.Category.ModuleCat.Ext.Basic

/-! The actual Ext carrier can have a universe independent of the ring and
of the modules in the finite presentation. -/

open CategoryTheory

universe u v w t s

example (R : Type u) [CommRing R] [IsLocalRing R]
    [HasExt.{w} (ModuleCat.{v} R)] (X Y : ModuleCat.{v} R)
    [IsArtinian R (CategoryTheory.Abelian.Ext.{w} X Y 1)] [Nontrivial (CategoryTheory.Abelian.Ext.{w} X Y 1)] :
    ∃ e : IsLocalRing.ResidueField R →ₗ[R] CategoryTheory.Abelian.Ext.{w} X Y 1,
      Function.Injective e :=
  IsArtinian.exists_injective_residueField R (CategoryTheory.Abelian.Ext.{w} X Y 1)

example (R : Type u) [CommRing R] [IsLocalRing R]
    [HasExt.{w} (ModuleCat.{v} R)] (X Y : ModuleCat.{v} R)
    [IsArtinian R (CategoryTheory.Abelian.Ext.{w} X Y 1)] [Nontrivial (CategoryTheory.Abelian.Ext.{w} X Y 1)]
    (M : Type t) [AddCommGroup M] [Module R M] [Module.Flat R M]
    (N : Type s) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (hf : Function.Injective (f.lTensor (CategoryTheory.Abelian.Ext.{w} X Y 1))) :
    Function.Injective (f.lTensor (IsLocalRing.ResidueField R)) :=
  IsArtinian.injective_lTensor_residueField_of_injective f hf
