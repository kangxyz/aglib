/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.RootsOfUnity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ZModLinear

/-!
# Tests for the `ℤ/n`-linearity of the duality pairing

The examples take an open immersion `j : U ⟶ X`, `Λ = ULift (ZMod n)`, `G = μ_n` and `d = 2`:
`Ext^s_{U,n}(F, μ_n)` and `H^r_c(U, F)` are killed by `n`, and the degree-two dual and
transposed maps are `ZMod n`-bilinear. They guard the axioms of every new declaration.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

namespace AglibTest.EtaleDualityZModLinear

attribute [local instance] hasSheafifyLarge moduleSheafExtZModModule

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ)

local instance (Y : Scheme.{u}) : HasExt.{u + 2} (ModuleSheaf Y (ULift.{u + 1} (ZMod n))) :=
  HasExt.standard _

local instance (Y : Scheme.{u}) : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Y) :=
  HasExt.standard _

/-- `n` kills `Ext^s_{U,n}(F, μ_n)`. -/
example (F : ModuleSheaf U (ULift.{u + 1} (ZMod n))) (s : ℕ)
    (e : Ext.{u + 2} F (moduleRootsOfUnity U n) s) : n • e = 0 :=
  moduleSheaf_uLiftZMod_ext_nsmul_eq_zero n e

/-- `n` kills the compactly supported cohomology `H^r_c(U, F₀)`. -/
example (F : ModuleSheaf U (ULift.{u + 1} (ZMod n))) (r : ℕ)
    (x : CompactSupport.H.{u + 2} j
      ((SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).obj F) r) :
    n • x = 0 :=
  compactSupport_uLiftZMod_nsmul_eq_zero j n F r x

/-- The degree-two dual map is `ZMod n`-bilinear. -/
example (F : ModuleSheaf U (ULift.{u + 1} (ZMod n))) (r : ℕ) (hr : r ≤ 2) (a : ZMod n)
    (c : Ext.{u + 2} (moduleUnit X (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j _).obj F) r)
    (e : Ext.{u + 2} F (moduleRootsOfUnity U n) (2 - r)) :
    moduleLowerShriekPairingDualLinearMap j n F (moduleRootsOfUnity U n) 2 r hr (a • c) e =
      a • moduleLowerShriekPairing j _ c e (by lia) := by
  rw [map_smul, LinearMap.smul_apply, moduleLowerShriekPairingDualLinearMap_apply_apply]

/-- The degree-two transposed map is `ZMod n`-bilinear. -/
example (F : ModuleSheaf U (ULift.{u + 1} (ZMod n))) (s : ℕ) (hs : s ≤ 2) (a : ZMod n)
    (e : Ext.{u + 2} F (moduleRootsOfUnity U n) s)
    (c : Ext.{u + 2} (moduleUnit X (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j _).obj F) (2 - s)) :
    moduleLowerShriekPairingTransposeLinearMap j n F (moduleRootsOfUnity U n) 2 s hs e
        (a • c) =
      a • moduleLowerShriekPairing j _ c e (by lia) := by
  rw [map_smul, moduleLowerShriekPairingTransposeLinearMap_apply_apply]

end AglibTest.EtaleDualityZModLinear

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleSheaf_uLiftZMod_nsmul_id_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleSheaf_uLiftZMod_nsmul_id_eq_zero

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleSheaf_uLiftZMod_ext_nsmul_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleSheaf_uLiftZMod_ext_nsmul_eq_zero

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleSheafExtZModModule' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleSheafExtZModModule

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.compactSupport_uLiftZMod_nsmul_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.compactSupport_uLiftZMod_nsmul_eq_zero

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.compactSupportZModModule' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.compactSupportZModModule

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingDualLinearMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingDualLinearMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingDualLinearMap_apply_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingDualLinearMap_apply_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingTransposeLinearMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingTransposeLinearMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingTransposeLinearMap_apply_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingTransposeLinearMap_apply_apply
