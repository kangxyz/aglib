/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ConstantPerfectness

/-! Original-map interfaces and approved-axiom guards. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

attribute [local instance] hasSheafifyLarge moduleSheafExtZModModule

universe u w w' w''
variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{w} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{w'} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{w''} (AbelianSheaf.{u, u + 1} X.left)]

/-- Degree-zero perfectness has no root choice, basis, purity or rank premise. -/
example : (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv
    (moduleUnit U (ULift.{u + 1} (ZMod n))) 0 (by decide)).IsPerfPair :=
  moduleDualityMap_unit_zero_isPerfPair X hX D hfin hclosed j hD n hn hunit hinv

/-- Degree-two perfectness retains all three independent Ext universes. -/
example : (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv
    (moduleUnit U (ULift.{u + 1} (ZMod n))) 2 le_rfl).IsPerfPair :=
  moduleDualityMap_unit_two_isPerfPair X hX D hfin hclosed j hD n hn hunit hinv

/-- The original transposed map is bijective into the native ZMod dual. -/
example : Function.Bijective (moduleDualityTransposeMap X hX D hfin hclosed j hD n hn hunit hinv
    (moduleUnit U (ULift.{u + 1} (ZMod n))) 0 (by decide)) :=
  (moduleDualityTransposeMap_unit_zero_isPerfPair X hX D hfin hclosed j hD n hn hunit
    hinv).bijective_left

omit [HasExt.{w} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{w'} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))] in
/-- The zero-ring level is covered by the same original pairing. -/
example [HasExt.{w} (ModuleSheaf U (ULift.{u + 1} (ZMod 1)))]
    [HasExt.{w'} (ModuleSheaf X.left (ULift.{u + 1} (ZMod 1)))] :
    (moduleDualityMap X hX D hfin hclosed j hD 1 (by decide) (by simp) (by simp)
      (moduleUnit U (ULift.{u + 1} (ZMod 1))) 2 le_rfl).IsPerfPair :=
  moduleDualityMap_unit_two_isPerfPair X hX D hfin hclosed j hD 1 (by decide) (by simp) (by simp)

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.nonempty_of_curve_finite_complement' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.nonempty_of_curve_finite_complement

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.connectedSpace_of_curve_finite_complement' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.connectedSpace_of_curve_finite_complement

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_unit_two_isPerfPair' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_unit_two_isPerfPair

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.subsingleton_moduleUnit_compactSupport_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.subsingleton_moduleUnit_compactSupport_zero

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.subsingleton_moduleUnit_roots_two' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.subsingleton_moduleUnit_roots_two

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_unit_zero_isPerfPair_of_isIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_unit_zero_isPerfPair_of_isIso

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_unit_zero_isPerfPair' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_unit_zero_isPerfPair

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_unit_zero_isPerfPair' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_unit_zero_isPerfPair

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_unit_two_isPerfPair' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_unit_two_isPerfPair
