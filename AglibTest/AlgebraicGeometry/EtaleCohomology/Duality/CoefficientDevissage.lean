/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.CoefficientDevissage

/-! The actual native coefficient rows, without a supplied commutative diagram. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wU wX wA

attribute [local instance] hasSheafifyLarge hasSheafifyModules moduleSheafExtZModModule

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]

example {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact)
    (hB : Function.Surjective (moduleDualityTransposeMap X hX D hfin hclosed j hD
      n hn hunit hinv S.X₂ 2 le_rfl)) :
    Function.Surjective (moduleDualityTransposeMap X hX D hfin hclosed j hD
      n hn hunit hinv S.X₁ 2 le_rfl) :=
  moduleDualityTransposeMap_two_surjective_of_shortExact
    X hX D hfin hclosed j hD n hn hunit hinv hS hB

example {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact)
    (hB₁ : Function.Surjective (moduleDualityTransposeMap X hX D hfin hclosed j hD
      n hn hunit hinv S.X₂ 1 (by decide)))
    (hC₂ : Function.Surjective (moduleDualityTransposeMap X hX D hfin hclosed j hD
      n hn hunit hinv S.X₃ 2 le_rfl))
    (hB₂ : Function.Injective (moduleDualityTransposeMap X hX D hfin hclosed j hD
      n hn hunit hinv S.X₂ 2 le_rfl)) :
    Function.Surjective (moduleDualityTransposeMap X hX D hfin hclosed j hD
      n hn hunit hinv S.X₁ 1 (by decide)) :=
  moduleDualityTransposeMap_one_surjective_of_shortExact
    X hX D hfin hclosed j hD n hn hunit hinv hS hB₁ hC₂ hB₂

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_two_surjective_of_shortExact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_two_surjective_of_shortExact

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_one_surjective_of_shortExact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_one_surjective_of_shortExact

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_one_injective_of_shortExact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_one_injective_of_shortExact
