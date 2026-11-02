/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.PointPurity

/-! # Original point-support module Ext and Kummer point normalization -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wM wA

attribute [local instance] hasSheafifyLarge hasSheafifyModules

section ProperPoint

variable {k : Type u} [Field k] [IsAlgClosed k] {C : FScheme k}
  (hC : Curve.Properties C) (x : Scheme.ClosedPoint C.left)
  {Z : Scheme.{u}} (i : Z ⟶ C.left) [IsClosedImmersion i]
  (hi : Set.range i = {x.val}) (n : ℕ) (hn : 0 < n)
  (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(C.left, ⊤)))
  [HasExt.{wM} (ModuleSheaf C.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} C.left)]

include hC x hi hn hunit hinv

example : Subsingleton (CategoryTheory.Abelian.Ext.{wM}
    ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
      (moduleUnit Z (ULift.{u + 1} (ZMod n)))) (moduleRootsOfUnity C.left n) 0) :=
  modulePointExt_zero_subsingleton hC x i hi n hn hunit hinv

example : CategoryTheory.Abelian.Ext.{wM}
    ((moduleDirectImage i (ULift.{u + 1} (ZMod n))).obj
      (moduleUnit Z (ULift.{u + 1} (ZMod n)))) (moduleRootsOfUnity C.left n) 2 ≃+ ZMod n :=
  modulePointPurityAddEquiv hC x i hi n hn hunit hinv

example : modulePointPurityAddEquiv hC x i hi n hn hunit hinv
    (modulePointPurityClass hC x i hi n hn hunit hinv) = 1 :=
  modulePointPurityAddEquiv_pointClass hC x i hi n hn hunit hinv

end ProperPoint

section OpenPoint

variable {k : Type u} [Field k] [IsAlgClosed k] {C : FScheme k}
  (hC : Curve.Properties C) {U : Scheme.{u}} (j : U ⟶ C.left) [IsOpenImmersion j]
  (x : Scheme.ClosedPoint U) (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  [HasExt.{wM} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]

include hC j x hn hunit

example : Subsingleton (CategoryTheory.Abelian.Ext.{wM}
    ((moduleDirectImage (U.fromSpecResidueField x.val) (ULift.{u + 1} (ZMod n))).obj
      (moduleUnit (Spec (U.residueField x.val)) (ULift.{u + 1} (ZMod n))))
    (moduleRootsOfUnity U n) 0) :=
  moduleOpenPointExt_zero_subsingleton hC j x n hn hunit

example : Subsingleton (CategoryTheory.Abelian.Ext.{wM}
    ((moduleDirectImage (U.fromSpecResidueField x.val) (ULift.{u + 1} (ZMod n))).obj
      (moduleUnit (Spec (U.residueField x.val)) (ULift.{u + 1} (ZMod n))))
    (moduleRootsOfUnity U n) 1) :=
  moduleOpenPointExt_one_subsingleton hC j x n hn hunit

example : CategoryTheory.Abelian.Ext.{wM}
    ((moduleDirectImage (U.fromSpecResidueField x.val) (ULift.{u + 1} (ZMod n))).obj
      (moduleUnit (Spec (U.residueField x.val)) (ULift.{u + 1} (ZMod n))))
    (moduleRootsOfUnity U n) 2 ≃+ ZMod n :=
  moduleOpenPointPurityAddEquiv hC j x n hn hunit

example : moduleOpenPointPurityAddEquiv hC j x n hn hunit
    (moduleOpenPointPurityClass hC j x n hn hunit) = 1 :=
  moduleOpenPointPurityAddEquiv_pointClass hC j x n hn hunit

example (q : ℕ) (hq : 2 < q) : Subsingleton (CategoryTheory.Abelian.Ext.{wM}
    ((moduleDirectImage (U.fromSpecResidueField x.val) (ULift.{u + 1} (ZMod n))).obj
      (moduleUnit (Spec (U.residueField x.val)) (ULift.{u + 1} (ZMod n))))
    (moduleRootsOfUnity U n) q) :=
  moduleOpenPointExt_high_subsingleton hC j x n hn hunit q hq

end OpenPoint

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.modulePointExtExcisionAddEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.modulePointExtExcisionAddEquiv

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleOpenPointPurityAddEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleOpenPointPurityAddEquiv

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleOpenPointPurityAddEquiv_pointClass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleOpenPointPurityAddEquiv_pointClass

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleOpenPointExt_high_subsingleton' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleOpenPointExt_high_subsingleton
