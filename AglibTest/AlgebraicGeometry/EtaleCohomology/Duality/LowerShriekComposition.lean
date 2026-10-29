/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.LowerShriekComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.RootsOfUnity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ModuleShortExact

/-!
# Tests for the Yoneda pairing along a composite extension by zero

The examples take open immersions `jV : V ⟶ U`, `jU : U ⟶ X`, `Λ = ULift (ZMod n)` and the
coefficient `μ_n` on `U`: the degree-two pairing on `U` for `jV_! A` is the pairing on `V` for
`A` followed by the counit (Milne, *Lectures on Étale Cohomology* v2.21, Thm. 14.7, proof,
Step 2, p. 94), and the squares of `moduleLowerShriekPairingDualHom` apply to the module
localization sequence on `U`. They guard the axioms of every new declaration.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

namespace AglibTest.EtaleDualityLowerShriekComposition

attribute [local instance] hasSheafifyLarge

variable {V U X : Scheme.{u}} (jV : V ⟶ U) [IsOpenImmersion jV] (jU : U ⟶ X)
  [IsOpenImmersion jU] (n : ℕ)

local instance (Y : Scheme.{u}) : HasExt.{u + 2} (ModuleSheaf Y (ULift.{u + 1} (ZMod n))) :=
  HasExt.standard _

/-- In degree two with `G = μ_n`: `φ_U(c, e) = φ_V(c', e') ∘ (compIso.hom ≫ jU_! ε)`. -/
example (A : ModuleSheaf V (ULift.{u + 1} (ZMod n))) (r : ℕ) (hr : r ≤ 2)
    (c : Ext.{u + 2} (moduleUnit X (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek jU _).obj ((moduleLowerShriek jV _).obj A)) r)
    (e : Ext.{u + 2} ((moduleLowerShriek jV _).obj A) (moduleRootsOfUnity U n) (2 - r)) :
    moduleLowerShriekPairing jU _ c e (by lia) =
      (moduleLowerShriekPairing (jV ≫ jU) _ (moduleLowerShriekCompAddEquiv jV jU _ A r c)
          (moduleLowerShriekExtEquiv jV _ A (moduleRootsOfUnity U n) (2 - r) e) (by lia)).comp
        (Ext.mk₀ ((moduleLowerShriekCompIso _ jU jV).hom.app
            ((moduleInverseImage jV _).obj (moduleRootsOfUnity U n)) ≫
          (moduleLowerShriek jU _).map
            ((moduleLowerShriekAdjunction jV _).counit.app (moduleRootsOfUnity U n))))
        (add_zero 2) :=
  moduleLowerShriekPairing_eq_comp_counit c e (by lia)

/-- The square of the degree-two dual homomorphism against the one on `V`. -/
example (A : ModuleSheaf V (ULift.{u + 1} (ZMod n))) (r : ℕ) (hr : r ≤ 2)
    (c : Ext.{u + 2} (moduleUnit X (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek jU _).obj ((moduleLowerShriek jV _).obj A)) r) :
    moduleLowerShriekPairingDualHom jU _ ((moduleLowerShriek jV _).obj A)
        (moduleRootsOfUnity U n) 2 r hr c =
      ((Ext.mk₀ ((moduleLowerShriekCompIso _ jU jV).hom.app
            ((moduleInverseImage jV _).obj (moduleRootsOfUnity U n)) ≫
          (moduleLowerShriek jU _).map
            ((moduleLowerShriekAdjunction jV _).counit.app (moduleRootsOfUnity U n)))).postcomp
          (moduleUnit X (ULift.{u + 1} (ZMod n))) (add_zero 2)).comp
        ((moduleLowerShriekPairingDualHom (jV ≫ jU) _ A
            ((moduleInverseImage jV _).obj (moduleRootsOfUnity U n)) 2 r hr
            (moduleLowerShriekCompAddEquiv jV jU _ A r c)).comp
          (moduleLowerShriekExtEquiv jV _ A (moduleRootsOfUnity U n) (2 - r)).toAddMonoidHom) :=
  moduleLowerShriekPairingDualHom_eq_comp_counit jV jU _ A (moduleRootsOfUnity U n) 2 r hr c

/-- The module localization sequence on `U` is short exact, so the connecting square of the
degree-two dual homomorphism applies to it. -/
example {Z : Scheme.{u}} (i : Z ⟶ U) [IsClosedImmersion i]
    (hcomp : Set.range jV = (Set.range i)ᶜ) (F : ModuleSheaf U (ULift.{u + 1} (ZMod n)))
    (r : ℕ) (hr : r + 1 ≤ 2)
    (c : Ext.{u + 2} (moduleUnit X (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek jU _).obj
        ((moduleLocalizationShortComplex jV (ULift.{u + 1} (ZMod n)) i hcomp F).X₃)) r) :
    moduleLowerShriekPairingDualHom jU _ _ (moduleRootsOfUnity U n) 2 (r + 1) hr
        (c.comp (shortExact_moduleLowerShriek jU _
          (moduleLocalization_shortExact jV _ i hcomp F)).extClass rfl) =
      (moduleLowerShriekPairingDualHom jU _ _ (moduleRootsOfUnity U n) 2 r (by lia) c).comp
        ((moduleLocalization_shortExact jV _ i hcomp F).extClass.precomp
          (moduleRootsOfUnity U n) (show 1 + (2 - (r + 1)) = 2 - r by lia)) :=
  moduleLowerShriekPairingDualHom_extClass (moduleLocalization_shortExact jV _ i hcomp F)
    (moduleRootsOfUnity U n) 2 r hr c

end AglibTest.EtaleDualityLowerShriekComposition

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekCompAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekCompAddEquiv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekCompAddEquiv_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekCompAddEquiv_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekCompAddEquiv_symm_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekCompAddEquiv_symm_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairing_moduleLowerShriekExt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairing_moduleLowerShriekExt

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairing_eq_comp_counit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairing_eq_comp_counit

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingDualHom_eq_comp_counit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingDualHom_eq_comp_counit
