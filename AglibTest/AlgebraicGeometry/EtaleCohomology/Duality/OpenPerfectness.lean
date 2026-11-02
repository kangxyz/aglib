/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.OpenPerfectness

/-! Both original open-unit adjoints at independent source and compact worlds. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wU wX wA

attribute [local instance] hasSheafifyLarge hasSheafifyModules moduleSheafExtZModModule

example {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
    (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
    {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
    [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)] (r : ℕ) (hr : r ≤ 2) :
    (moduleDualityMap.{u, wU, wX, wA} X hX D hfin hclosed j hD n hn hunit hinv
      (moduleUnit U (ULift.{u + 1} (ZMod n))) r hr).IsPerfPair :=
  moduleDualityMap_unit_open_isPerfPair.{u, wU, wX, wA}
    X hX D hfin hclosed j hD n hn hunit hinv r hr

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_unit_open_one_isPerfPair' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_unit_open_one_isPerfPair

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_unit_open_isPerfPair' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_unit_open_isPerfPair


section FiniteLocalSystems

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]
  (F : ModuleSheaf U (ULift.{u + 1} (ZMod n)))
  (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
    ((moduleSheafEquivalence U (ULift.{u + 1} (ZMod n))).inverse.obj F))

example : Function.Bijective (moduleDualityTransposeMap.{u, wU, wX, wA}
    X hX D hfin hclosed j hD n hn hunit hinv F 0 (by decide)) :=
  moduleDualityTransposeMap_open_zero_bijective.{u, wU, wX, wA}
    X hX D hfin hclosed j hD n hn hunit hinv F hF

example : Function.Bijective (moduleDualityTransposeMap.{u, wU, wX, wA}
    X hX D hfin hclosed j hD n hn hunit hinv F 1 (by decide)) :=
  moduleDualityTransposeMap_open_one_bijective.{u, wU, wX, wA}
    X hX D hfin hclosed j hD n hn hunit hinv F hF

example : Function.Bijective (moduleDualityTransposeMap.{u, wU, wX, wA}
    X hX D hfin hclosed j hD n hn hunit hinv F 2 (by decide)) :=
  moduleDualityTransposeMap_open_two_bijective.{u, wU, wX, wA}
    X hX D hfin hclosed j hD n hn hunit hinv F hF

omit [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))] in
example (q : ℕ) : Finite (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
    ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj F) q) :=
  moduleCompactExt_finite_of_finiteLocallyConstant
    X hX D hfin hclosed j hD n hn hunit F hF q

example (r : ℕ) (hr : r ≤ 2) :
    (moduleDualityMap.{u, wU, wX, wA} X hX D hfin hclosed j hD
      n hn hunit hinv F r hr).IsPerfPair :=
  moduleDualityMap_isPerfPair_of_finiteLocallyConstant.{u, wU, wX, wA}
    X hX D hfin hclosed j hD n hn hunit hinv F hF r hr

end FiniteLocalSystems

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleSourceExt_open_high_subsingleton_of_finiteLocallyConstant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleSourceExt_open_high_subsingleton_of_finiteLocallyConstant

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_open_zero_bijective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_open_zero_bijective

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_open_two_bijective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_open_two_bijective

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_open_one_bijective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_open_one_bijective

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleCompactExt_finite_of_finiteLocallyConstant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleCompactExt_finite_of_finiteLocallyConstant

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_isPerfPair_of_finiteLocallyConstant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_isPerfPair_of_finiteLocallyConstant
