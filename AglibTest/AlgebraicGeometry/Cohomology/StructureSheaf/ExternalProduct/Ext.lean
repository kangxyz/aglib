/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct.Ext

/-! Native consumers use the two original projection maps and the genuine
external-tensor Ext constructor, with no supplied interchange condition. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Cohomology AlgebraicGeometry.Scheme.Modules

attribute [local instance] Over.cartesianMonoidalCategory

universe u
variable {k : Type u} [Field k] (X Y : FScheme k)

example {p q n : ℕ} (h : p + q = n)
    (x : Scheme.structureCohomology k X p) (y : Scheme.structureCohomology k Y q) :
    structureExternalCup X Y h x y = ((-1 : ℤ) ^ (p * q)) •
      structureCup (X ⊗ Y) ((Nat.add_comm q p).trans h)
        (structureCohomologyPullbackLinear (snd X Y) q y)
        (structureCohomologyPullbackLinear (fst X Y) p x) :=
  structureCup_fst_snd_comm X Y h x y

example {p q n : ℕ} (h : p + q = n)
    (x : Ext.{u + 1} (C := X.left.Modules) (SheafOfModules.unit X.left.ringCatSheaf)
      (SheafOfModules.unit X.left.ringCatSheaf) p)
    (y : Ext.{u + 1} (C := Y.left.Modules) (SheafOfModules.unit Y.left.ringCatSheaf)
      (SheafOfModules.unit Y.left.ringCatSheaf) q) :
    let e := externalTensorUnitIso X.hom Y.hom
    structureExternalCup X Y h (structureExtLinearEquiv X p x)
        (structureExtLinearEquiv Y q y) =
      structureExtLinearEquiv (X ⊗ Y) n
        (((Ext.mk₀ e.inv).comp ((externalTensor X.hom Y.hom).extBifunctor x y h)
          (Nat.zero_add n)).comp (Ext.mk₀ e.hom) (Nat.add_zero n)) :=
  structureExternalCup_eq_extBifunctor X Y h x y
