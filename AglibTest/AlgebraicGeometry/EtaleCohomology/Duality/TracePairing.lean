/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.TracePairing

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

/-- The whole map is the actual Yoneda bilinear map followed by the original trace. -/
example (F : ModuleSheaf U (ULift.{u + 1} (ZMod n))) (r : ℕ) (hr : r ≤ 2) :
    moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv F r hr =
      (moduleLowerShriekPairingDualLinearMap j n F (moduleRootsOfUnity U n) 2 r hr).compr₂
        (moduleCompactSupportTraceLinearMap X hX D hfin hclosed j hD n hn hunit hinv) :=
  moduleDualityMap_eq X hX D hfin hclosed j hD n hn hunit hinv F r hr

/-- Evaluation against the actual roots identity retains the exact normalized trace. -/
example :
    (moduleTracePairingLinearMap X hX D hfin hclosed j hD n hn hunit hinv
      (moduleRootsOfUnity U n) 2 0 rfl).flip (Ext.mk₀ (𝟙 (moduleRootsOfUnity U n))) =
      moduleCompactSupportTraceLinearMap X hX D hfin hclosed j hD n hn hunit hinv :=
  moduleTracePairingLinearMap_mk₀_id X hX D hfin hclosed j hD n hn hunit hinv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleTracePairingLinearMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleTracePairingLinearMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleTracePairingLinearMap_apply_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleTracePairingLinearMap_apply_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_eq

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_eq

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleTracePairingLinearMap_naturality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleTracePairingLinearMap_naturality

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleTracePairingLinearMap_extClass' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleTracePairingLinearMap_extClass

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleTracePairingLinearMap_δ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleTracePairingLinearMap_δ

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleTracePairingLinearMap_mk₀_left' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleTracePairingLinearMap_mk₀_left

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleTracePairingLinearMap_smul_mk₀' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleTracePairingLinearMap_smul_mk₀

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleTracePairingLinearMap_mk₀_id' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleTracePairingLinearMap_mk₀_id
