/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.FiniteCoefficientsVanishing.Open

/-! Ordinary finite-type-curve high vanishing on the original native Ext carrier. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology

universe u w w'

attribute [local instance] hasSheafifyLarge Coefficients.hasSheafifyModules

example {k : Type u} [Field k] [IsSepClosed k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [CompactSpace X] [ConnectedSpace X]
    (hdim : topologicalKrullDim X ≤ 1) (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (Coefficients.ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
    (q : ℕ) (hq : 2 < q) (M : Coefficients.ModuleSheaf X (ULift.{u + 1} (ZMod n)))
    (hM : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((Coefficients.moduleSheafEquivalence X (ULift.{u + 1} (ZMod n))).inverse.obj M)) :
    Subsingleton (CategoryTheory.Abelian.Ext.{w'}
      (moduleUnit X (ULift.{u + 1} (ZMod n))) M q) :=
  Curves.moduleUnitExt_high_subsingleton_of_finiteType_curve X f hdim n hn hunit q hq M hM

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.dimension_le_one_of_etale' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.dimension_le_one_of_etale

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.primeField_high_subsingleton_of_finiteType_curve' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.primeField_high_subsingleton_of_finiteType_curve

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.moduleSheaf_high_subsingleton_of_finiteType_curve' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.moduleSheaf_high_subsingleton_of_finiteType_curve

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.uLiftZMod_moduleSheaf_high_subsingleton_of_finiteType_curve' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.uLiftZMod_moduleSheaf_high_subsingleton_of_finiteType_curve

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.moduleUnitExt_high_subsingleton_of_finiteType_curve' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.moduleUnitExt_high_subsingleton_of_finiteType_curve
