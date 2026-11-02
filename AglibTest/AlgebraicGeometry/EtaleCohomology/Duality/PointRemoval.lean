/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.PointRemoval

/-! The actual point-supported pairing, with independent Ext worlds. -/

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

/-- The point is the original residue-field point of the given open. -/
example (x : Scheme.ClosedPoint U) :
    (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv
      ((moduleDirectImage (U.fromSpecResidueField x.val) (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit (Spec (U.residueField x.val)) (ULift.{u + 1} (ZMod n))))
          0 (by decide)).IsPerfPair :=
  moduleDualityMap_point_zero_isPerfPair X hX D hfin hclosed j hD n hn hunit hinv x

/-- Both original adjoints are bijective in every allowed point degree. -/
example (x : Scheme.ClosedPoint U) (r : ℕ) (hr : r ≤ 2) :
    (moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv
      ((moduleDirectImage (U.fromSpecResidueField x.val) (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit (Spec (U.residueField x.val)) (ULift.{u + 1} (ZMod n)))) r hr).IsPerfPair :=
  moduleDualityMap_point_isPerfPair X hX D hfin hclosed j hD n hn hunit hinv x r hr

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleTracePairingLinearMap_compactPointUnit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleTracePairingLinearMap_compactPointUnit

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_point_zero_isPerfPair' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_point_zero_isPerfPair

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_point_isPerfPair' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_point_isPerfPair
