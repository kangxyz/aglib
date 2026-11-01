/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ConstantOnePerfectness

/-! The actual unsigned source-boundary reduction with independent Ext worlds. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u w w' w''

attribute [local instance] hasSheafifyLarge moduleSheafExtZModModule

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{w} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{w'} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{w''} (AbelianSheaf.{u, u + 1} X.left)]

/-- The reduction takes only actual degree-zero conclusions and the two
original vanishing assertions; it has no diagram-commutativity premise. -/
example {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact)
    (hB : Function.Surjective (moduleDualityTransposeMap X hX D hfin hclosed j hD
      n hn hunit hinv S.X₂ 0 (by decide)))
    (hK : Function.Injective (moduleDualityTransposeMap X hX D hfin hclosed j hD
      n hn hunit hinv S.X₁ 0 (by decide)))
    (e : Ext.{w} S.X₃ (moduleRootsOfUnity U n) 1)
    (he : (Ext.mk₀ S.g).comp e (zero_add 1) = 0)
    (hzero : moduleDualityTransposeMap X hX D hfin hclosed j hD n hn hunit hinv
      S.X₃ 1 (by decide) e = 0) : e = 0 :=
  moduleDualityTransposeMap_one_eq_zero_of_precomp_eq_zero X hX D hfin hclosed j hD
    n hn hunit hinv hS hB hK e he hzero

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_one_eq_zero_of_precomp_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_one_eq_zero_of_precomp_eq_zero

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.exists_galois_finiteEtale_moduleRoots_one_killed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.exists_galois_finiteEtale_moduleRoots_one_killed

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.exists_galois_finiteEtale_unitCounit_one_killed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.exists_galois_finiteEtale_unitCounit_one_killed

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnit_one_finite_and_natCard_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnit_one_finite_and_natCard_eq

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitCompactIdExt_subsingleton_of_finiteLocallyConstant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitCompactIdExt_subsingleton_of_finiteLocallyConstant
