/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.PairingRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.RootsOfUnity

/-!
# Tests for the transposed duality map and restriction to an open subscheme

The example takes open immersions `jV : V ⟶ U`, `jU : U ⟶ X`, `Λ = ULift (ZMod n)`,
`G = μ_n` and `d = 2`: the square of Milne's `ψ` against restriction to `V` (*Lectures on Étale
Cohomology* v2.21, Thm. 14.7, proof, Step 2, p. 94), and guards the axioms of every new
declaration.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

namespace AglibTest.EtaleDualityPairingRestriction

attribute [local instance] hasSheafifyLarge

variable {V U X : Scheme.{u}} (jV : V ⟶ U) [IsOpenImmersion jV] (jU : U ⟶ X)
  [IsOpenImmersion jU] (n : ℕ)

local instance (Y : Scheme.{u}) : HasExt.{u + 2} (ModuleSheaf Y (ULift.{u + 1} (ZMod n))) :=
  HasExt.standard _

/-- The degree-two square of `ψ` against restriction to `V`, for `G = μ_n`. -/
example (F : ModuleSheaf U (ULift.{u + 1} (ZMod n))) (s : ℕ) (hs : s ≤ 2)
    (e : Ext.{u + 2} F (moduleRootsOfUnity U n) s) :
    (moduleLowerShriekPairingTransposeHom jU _ F (moduleRootsOfUnity U n) 2 s hs e).comp
        ((Ext.mk₀ ((moduleLowerShriekCompIso _ jU jV).hom.app ((moduleInverseImage jV _).obj F) ≫
          (moduleLowerShriek jU _).map ((moduleLowerShriekAdjunction jV _).counit.app F))).postcomp
          (moduleUnit X (ULift.{u + 1} (ZMod n))) (add_zero (2 - s))) =
      ((Ext.mk₀ ((moduleLowerShriekCompIso _ jU jV).hom.app
            ((moduleInverseImage jV _).obj (moduleRootsOfUnity U n)) ≫
          (moduleLowerShriek jU _).map
            ((moduleLowerShriekAdjunction jV _).counit.app (moduleRootsOfUnity U n)))).postcomp
          (moduleUnit X (ULift.{u + 1} (ZMod n))) (add_zero 2)).comp
        (moduleLowerShriekPairingTransposeHom (jV ≫ jU) _ ((moduleInverseImage jV _).obj F)
          ((moduleInverseImage jV _).obj (moduleRootsOfUnity U n)) 2 s hs
          (moduleLowerShriekExtEquiv jV _ ((moduleInverseImage jV _).obj F)
            (moduleRootsOfUnity U n) s
            ((Ext.mk₀ ((moduleLowerShriekAdjunction jV _).counit.app F)).comp e (zero_add s)))) :=
  moduleLowerShriekPairingTransposeHom_restriction F (moduleRootsOfUnity U n) 2 s hs e

end AglibTest.EtaleDualityPairingRestriction

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingTransposeHom_restriction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingTransposeHom_restriction

