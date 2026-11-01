/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.LocallyConstantPerfectness

/-! Original finite support, compact unit vanishing and smaller-open pairing comparisons. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wU wX wA wP

attribute [local instance] hasSheafifyLarge hasSheafifyModules moduleSheafExtZModModule

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]

/-- The original support model and whole SUM include empty finite support. -/
example (T : Set U) (hTfin : T.Finite)
    (hTclosed : ∀ x ∈ T, IsClosed ({x} : Set U)) (r : ℕ) (hr : r ≤ 2) :
    (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv
      (moduleFinitePointSource U T n) r hr).IsPerfPair :=
  moduleDualityMap_finitePoint_isPerfPair X hX D hfin hclosed j hD n hn hunit hinv
    T hTfin hTclosed r hr

/-- Constant compact high vanishing uses the proper unit, never local
constancy of its extension by zero. -/
example (q : ℕ) (hq : 2 < q) :
    Subsingleton (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit U (ULift.{u + 1} (ZMod n)))) q) :=
  moduleUnitCompactExt_high_subsingleton X hX D hfin hclosed j hD n hn hunit q hq


/-- Every original finite locally constant coefficient has genuine compact
vanishing above degree two, with independent module and abelian Ext worlds. -/
example (F : ModuleSheaf U (ULift.{u + 1} (ZMod n)))
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence U (ULift.{u + 1} (ZMod n))).inverse.obj F))
    (q : ℕ) (hq : 2 < q) :
    Subsingleton (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj F) q) :=
  moduleCompactExt_high_subsingleton_of_finiteLocallyConstant
    X hX D hfin hclosed j hD n hn hunit F hF q hq

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleCompactExt_high_subsingleton_of_finiteLocallyConstant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleCompactExt_high_subsingleton_of_finiteLocallyConstant

variable [HasExt.{wP} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]

/-- Proper source degree zero uses the actual free cover and proper kernel
vanishing, with independent source and compact Ext worlds. -/
example (F : ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X.left (ULift.{u + 1} (ZMod n))).inverse.obj F)) :
    Function.Bijective (moduleDualityTransposeMap.{u, wP, wX, wA}
      X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp)
      n hn hunit hinv F 0 (by decide)) :=
  moduleDualityTransposeMap_proper_zero_bijective.{u, wX, wA, wP} X hX n hn hunit hinv F hF

/-- Both original proper unit-H1 adjoints are perfect at every positive
invertible level, including composite levels and level one. -/
example : (moduleDualityMap.{u, wP, wX, wA}
    X hX ∅ Set.finite_empty (by simp) (𝟙 X.left) (by simp)
    n hn hunit hinv (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
    1 (by decide)).IsPerfPair :=
  moduleDualityMap_unit_proper_one_isPerfPair.{u, wX, wA, wP} X hX n hn hunit hinv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_proper_zero_bijective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_proper_zero_bijective

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_unit_proper_one_isPerfPair' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_unit_proper_one_isPerfPair
