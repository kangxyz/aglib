/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.PairingTranspose
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootsOfUnity

/-!
# Tests for the transposed duality map

The examples take an open immersion `j : U ⟶ X`, `Λ = ULift (ZMod n)`, `G = μ_n` and `d = 2`:
the map `Ext^s_{U,n}(F, μ_n) → Hom(H^{2-s}_c(U, F), H^2_c(U, μ_n))` in the direction of Milne's
`ψ` (*Lectures on Étale Cohomology* v2.21, Thm. 14.7, proof, p. 94) and its three squares. They
guard the axioms of every new declaration.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

namespace AglibTest.EtaleDualityPairingTranspose

attribute [local instance] hasSheafifyLarge

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ)

local instance (Y : Scheme.{u}) : HasExt.{u + 2} (ModuleSheaf Y (ULift.{u + 1} (ZMod n))) :=
  HasExt.standard _

/-- The transposed map `Ext^s_{U,n}(F, μ_n) → Hom(H^{2-s}_c(U, F), H^2_c(U, μ_n))`. -/
example (F : ModuleSheaf U (ULift.{u + 1} (ZMod n))) (s : ℕ) (hs : s ≤ 2)
    (e : Ext.{u + 2} F (moduleRootsOfUnity U n) s)
    (c : Ext.{u + 2} (moduleUnit X (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j _).obj F) (2 - s)) :
    moduleLowerShriekPairingTransposeHom j _ F (moduleRootsOfUnity U n) 2 s hs e c =
      moduleLowerShriekPairing j _ c e (by lia) :=
  moduleLowerShriekPairingTransposeHom_apply_apply j _ F _ 2 s hs e c

/-- The square against a coefficient map. -/
example {F F' : ModuleSheaf U (ULift.{u + 1} (ZMod n))} (f : F ⟶ F') (s : ℕ) (hs : s ≤ 2)
    (e' : Ext.{u + 2} F' (moduleRootsOfUnity U n) s) :
    moduleLowerShriekPairingTransposeHom j _ F (moduleRootsOfUnity U n) 2 s hs
        ((Ext.mk₀ f).comp e' (zero_add s)) =
      (moduleLowerShriekPairingTransposeHom j _ F' (moduleRootsOfUnity U n) 2 s hs e').comp
        ((Ext.mk₀ ((moduleLowerShriek j _).map f)).postcomp
          (moduleUnit X (ULift.{u + 1} (ZMod n))) (add_zero (2 - s))) :=
  moduleLowerShriekPairingTransposeHom_naturality f 2 s hs e'

/-- The connecting squares, against `extClass` (sign `+1`) and against `Ext.δ`. -/
example {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact)
    (s : ℕ) (hs : s + 1 ≤ 2) (e' : Ext.{u + 2} S.X₁ (moduleRootsOfUnity U n) s) :
    moduleLowerShriekPairingTransposeHom j _ S.X₃ (moduleRootsOfUnity U n) 2 (s + 1) hs
        (hS.extClass.comp e' (add_comm 1 s)) =
      (moduleLowerShriekPairingTransposeHom j _ S.X₁ (moduleRootsOfUnity U n) 2 s (by lia)
          e').comp
        ((shortExact_moduleLowerShriek j _ hS).extClass.postcomp
          (moduleUnit X (ULift.{u + 1} (ZMod n))) (show 2 - (s + 1) + 1 = 2 - s by lia)) ∧
    moduleLowerShriekPairingTransposeHom j _ S.X₃ (moduleRootsOfUnity U n) 2 (s + 1) hs
        (Ext.δ hS s (s + 1) rfl e') =
      ((s + 1 : ℕ) : ℤ).negOnePow •
        (moduleLowerShriekPairingTransposeHom j _ S.X₁ (moduleRootsOfUnity U n) 2 s (by lia)
          e').comp
          ((shortExact_moduleLowerShriek j _ hS).extClass.postcomp
            (moduleUnit X (ULift.{u + 1} (ZMod n))) (show 2 - (s + 1) + 1 = 2 - s by lia)) :=
  ⟨moduleLowerShriekPairingTransposeHom_extClass hS _ 2 s hs e',
    moduleLowerShriekPairingTransposeHom_δ hS _ 2 s hs e'⟩

end AglibTest.EtaleDualityPairingTranspose

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingTransposeHom' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingTransposeHom

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingTransposeHom_apply_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingTransposeHom_apply_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingTransposeHom_naturality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingTransposeHom_naturality

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingTransposeHom_extClass' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingTransposeHom_extClass

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingTransposeHom_δ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingTransposeHom_δ
