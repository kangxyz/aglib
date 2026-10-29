/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.RootsOfUnity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.YonedaPairing

/-!
# Tests for the Yoneda pairing of compactly supported cohomology with Ext

The examples take an open immersion `j : U ⟶ X`, `Λ = ULift (ZMod n)` and the coefficient
`μ_n` of `moduleRootsOfUnity`, giving the pairing
`H^r_c(U, F) × Ext^s_{U,n}(F, μ_n) → H^{r+s}_c(U, μ_n)` of Milne, *Lectures on Étale
Cohomology* (v2.21), p. 103, and its degree-two dual homomorphism (Thm 14.7, p. 93). They
guard the axioms of every new declaration.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

namespace AglibTest.EtaleDualityYonedaPairing

attribute [local instance] hasSheafifyLarge

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ)

local instance (Y : Scheme.{u}) : HasExt.{u + 2} (ModuleSheaf Y (ULift.{u + 1} (ZMod n))) :=
  HasExt.standard _

/-- The pairing `H^r_c(U, F) × Ext^s_{U,n}(F, μ_n) → H^{r+s}_c(U, μ_n)`, biadditively. -/
example (F : ModuleSheaf U (ULift.{u + 1} (ZMod n))) (r s : ℕ) :
    Ext.{u + 2} (moduleUnit X (ULift.{u + 1} (ZMod n))) ((moduleLowerShriek j _).obj F) r →+
      Ext.{u + 2} F (moduleRootsOfUnity U n) s →+
        Ext.{u + 2} (moduleUnit X (ULift.{u + 1} (ZMod n)))
          ((moduleLowerShriek j _).obj (moduleRootsOfUnity U n)) (r + s) :=
  moduleLowerShriekPairingHom j _ F (moduleRootsOfUnity U n) r s (r + s) rfl

/-- The induced map `H^r_c(U, F) → Hom(Ext^{2-r}_{U,n}(F, μ_n), H^2_c(U, μ_n))`, `r ≤ 2`. -/
example (F : ModuleSheaf U (ULift.{u + 1} (ZMod n))) (r : ℕ) (hr : r ≤ 2) :
    Ext.{u + 2} (moduleUnit X (ULift.{u + 1} (ZMod n))) ((moduleLowerShriek j _).obj F) r →+
      Ext.{u + 2} F (moduleRootsOfUnity U n) (2 - r) →+
        Ext.{u + 2} (moduleUnit X (ULift.{u + 1} (ZMod n)))
          ((moduleLowerShriek j _).obj (moduleRootsOfUnity U n)) 2 :=
  moduleLowerShriekPairingDualHom j _ F (moduleRootsOfUnity U n) 2 r hr

/-- The long exact sequence of `H_c` for a short exact sequence on `U` is Mathlib's covariant
Ext sequence of its extension by zero. -/
example {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact)
    (r : ℕ) :
    (Ext.covariantSequence (moduleUnit X (ULift.{u + 1} (ZMod n)))
      (shortExact_moduleLowerShriek j _ hS) r (r + 1) rfl).Exact :=
  Ext.covariantSequence_exact _ _ r (r + 1) rfl

/-- The long exact sequence of `Ext_{U,n}(-, μ_n)` is Mathlib's contravariant Ext sequence. -/
example {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact)
    (s : ℕ) : (Ext.contravariantSequence hS (moduleRootsOfUnity U n) s (1 + s) rfl).Exact :=
  Ext.contravariantSequence_exact hS _ s (1 + s) rfl

/-- Naturality: `φ(u_* c, e') = φ(c, u^* e')`. -/
example {F F' : ModuleSheaf U (ULift.{u + 1} (ZMod n))} (f : F ⟶ F') {r s : ℕ}
    (c : Ext.{u + 2} (moduleUnit X (ULift.{u + 1} (ZMod n))) ((moduleLowerShriek j _).obj F) r)
    (e' : Ext.{u + 2} F' (moduleRootsOfUnity U n) s) :
    moduleLowerShriekPairing j _
        (c.comp (Ext.mk₀ ((moduleLowerShriek j _).map f)) (add_zero r)) e' rfl =
      moduleLowerShriekPairing j _ c ((Ext.mk₀ f).comp e' (zero_add s)) rfl :=
  moduleLowerShriekPairing_naturality f c e' rfl

/-- Connecting maps, sign `+1`: `φ(δ c'', e') = φ(c'', δ e')`. -/
example {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact)
    {r s : ℕ} (c : Ext.{u + 2} (moduleUnit X (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j _).obj S.X₃) r) (e' : Ext.{u + 2} S.X₁ (moduleRootsOfUnity U n) s) :
    moduleLowerShriekPairing j _ (c.comp (shortExact_moduleLowerShriek j _ hS).extClass rfl) e'
        (rfl : r + 1 + s = r + 1 + s) =
      moduleLowerShriekPairing j _ c (hS.extClass.comp e' (add_comm 1 s)) (by lia) :=
  moduleLowerShriekPairing_extClass hS c e' rfl (add_comm 1 s) rfl (by lia)

/-- Connecting maps against Mathlib's signed `Ext.δ`: sign `(-1)^(s+1)`. -/
example {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact)
    {r s : ℕ} (c : Ext.{u + 2} (moduleUnit X (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j _).obj S.X₃) r) (e' : Ext.{u + 2} S.X₁ (moduleRootsOfUnity U n) s) :
    moduleLowerShriekPairing j _ c (Ext.δ hS s (s + 1) rfl e') (by lia : r + (s + 1) = r + 1 + s) =
      ((s + 1 : ℕ) : ℤ).negOnePow •
        moduleLowerShriekPairing j _ (c.comp (shortExact_moduleLowerShriek j _ hS).extClass rfl)
          e' rfl :=
  moduleLowerShriekPairing_δ hS c e' rfl rfl rfl (by lia)

/-- The degree-two squares against the connecting maps: sign `+1` and, for `Ext.δ`,
`(-1)^(2-r)`. -/
example {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact) (r : ℕ)
    (hr : r + 1 ≤ 2) (c : Ext.{u + 2} (moduleUnit X (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j _).obj S.X₃) r) :
    moduleLowerShriekPairingDualHom j _ S.X₁ (moduleRootsOfUnity U n) 2 (r + 1) hr
        (c.comp (shortExact_moduleLowerShriek j _ hS).extClass rfl) =
      (moduleLowerShriekPairingDualHom j _ S.X₃ (moduleRootsOfUnity U n) 2 r (by lia) c).comp
        (hS.extClass.precomp (moduleRootsOfUnity U n) (show 1 + (2 - (r + 1)) = 2 - r by lia)) ∧
    (moduleLowerShriekPairingDualHom j _ S.X₃ (moduleRootsOfUnity U n) 2 r (by lia) c).comp
        (Ext.δ hS (2 - (r + 1)) (2 - r) (by lia)) =
      ((2 - r : ℕ) : ℤ).negOnePow •
        moduleLowerShriekPairingDualHom j _ S.X₁ (moduleRootsOfUnity U n) 2 (r + 1) hr
          (c.comp (shortExact_moduleLowerShriek j _ hS).extClass rfl) :=
  ⟨moduleLowerShriekPairingDualHom_extClass hS _ 2 r hr c,
    moduleLowerShriekPairingDualHom_δ hS _ 2 r hr c⟩

/-- The degree-two square against a coefficient map. -/
example {F F' : ModuleSheaf U (ULift.{u + 1} (ZMod n))} (f : F ⟶ F') (r : ℕ) (hr : r ≤ 2)
    (c : Ext.{u + 2} (moduleUnit X (ULift.{u + 1} (ZMod n))) ((moduleLowerShriek j _).obj F) r) :
    moduleLowerShriekPairingDualHom j _ F' (moduleRootsOfUnity U n) 2 r hr
        (c.comp (Ext.mk₀ ((moduleLowerShriek j _).map f)) (add_zero r)) =
      (moduleLowerShriekPairingDualHom j _ F (moduleRootsOfUnity U n) 2 r hr c).comp
        ((Ext.mk₀ f).precomp (moduleRootsOfUnity U n) (zero_add (2 - r))) :=
  moduleLowerShriekPairingDualHom_naturality f 2 r hr c

end AglibTest.EtaleDualityYonedaPairing

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekPairing

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairing_def' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekPairing_def

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekPairingHom

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingHom_apply_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekPairingHom_apply_apply

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairing_add_left' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekPairing_add_left

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairing_add_right' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekPairing_add_right

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairing_zero_left' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekPairing_zero_left

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairing_zero_right' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekPairing_zero_right

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairing_neg_left' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekPairing_neg_left

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairing_neg_right' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekPairing_neg_right

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairing_zsmul_right' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekPairing_zsmul_right

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairing_naturality' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekPairing_naturality

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairing_comp_mk₀' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekPairing_comp_mk₀

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairing_extClass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekPairing_extClass

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairing_δ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekPairing_δ

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingDualHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekPairingDualHom

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingDualHom_apply_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekPairingDualHom_apply_apply

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingDualHom_naturality' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekPairingDualHom_naturality

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingDualHom_extClass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekPairingDualHom_extClass

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekPairingDualHom_δ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekPairingDualHom_δ
