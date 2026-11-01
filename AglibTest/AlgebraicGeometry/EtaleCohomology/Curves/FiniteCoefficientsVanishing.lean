/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.FiniteCoefficientsVanishing

/-! Proper-curve vanishing on the original module-cohomology carriers. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r w w'

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k)
  (hX : Curve.Properties X) [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)]

/-- The finite étale source has actual curve properties with no supplied point. -/
example (Y : Scheme.FiniteEtale X.left) [ConnectedSpace Y.obj.left] :
    Curve.Properties (Over.mk (Y.obj.hom ≫ X.hom)) :=
  Curves.curveProperties_of_connected_finiteEtale X hX Y

/-- The prime stage uses the genuine coefficient module and its original action. -/
example (R : Type r) [CommRing R] [Finite R]
    (p : ℕ) [Fact p.Prime] (hunit : IsUnit (p : k))
    (M : ModuleCat.{u + 1} R) [Module.Finite R M] (hM : ∀ m : M, p • m = 0) :
    Subsingleton ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R 3).obj
      ((constantSheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)) :=
  Curves.constantModuleSheaf_subsingleton_H_of_prime_nsmul X hX R p hunit 3 (by decide) M hM

/-- The original native unit-Ext carrier in degree three, at independent
module and abelian Ext universes, has no supplied global-cover premise. -/
example (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
    [HasExt.{w'} (Coefficients.ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
    (M : Coefficients.ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))
    (hM : IsFiniteTypeLocallyConstant
      ((Coefficients.moduleSheafEquivalence X.left (ULift.{u + 1} (ZMod n))).inverse.obj M)) :
    Subsingleton (CategoryTheory.Abelian.Ext.{w'}
      (moduleUnit X.left (ULift.{u + 1} (ZMod n))) M 3) :=
  Curves.moduleUnitExt_subsingleton_of_finiteLocallyConstant X hX n hn hunit 3 (by decide) M hM

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.moduleSheaf_subsingleton_H_of_pGroup_trivialization' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.moduleSheaf_subsingleton_H_of_pGroup_trivialization

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.moduleSheaf_subsingleton_H_of_galois_prime_trivialization' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.moduleSheaf_subsingleton_H_of_galois_prime_trivialization

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.moduleUnitExt_subsingleton_of_finiteLocallyConstant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.moduleUnitExt_subsingleton_of_finiteLocallyConstant
