/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.LocalHomExactness
public import Aglib.Algebra.Module.ZMod.Injective

/-! # Native local-Ext supplier tests and standard axiom guards -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c h

/-- The actual positive composite-level self-injectivity supplies the local induction target. -/
example {C : Type c} [Category.{h} C] (J : GrothendieckTopology C) (n : ℕ) [NeZero n]
    (I : CochainComplex (Sheaf J (ModuleCat.{max c h} (ZMod n))) ℕ)
    (N : Sheaf J (ModuleCat.{max c h} (ZMod n)))
    (η : (Functor.const Cᵒᵖ).obj
      (ModuleCat.of (ZMod n) (ULift.{max c h} (ZMod n))) ⟶ N.obj)
    [CategoryTheory.Presheaf.IsLocallySurjective J η]
    [CategoryTheory.Presheaf.IsLocallyInjective J η]
    (i : N ⟶ I.X 0) (hi : i ≫ I.d 0 1 = 0) [Mono i]
    (hN : (ShortComplex.mk i (I.d 0 1) hi).Exact)
    (hI : ∀ q : ℕ, I.ExactAt (q + 1))
    [∀ (q : ℕ) (U : C), Injective ((I.X q).obj.obj (op U))]
    (M : ModuleCat.{max c h} (ZMod n)) [Module.Finite (ZMod n) M] (q : ℕ) :
    ModuleCat.Sheaf.LocallyBoundary J I M q := by
  let : Module.Injective (ZMod n) (ZMod n) := ZMod.injective_self n
  let : Injective (ModuleCat.of (ZMod n) (ZMod n)) :=
    Module.injective_object_of_injective_module (ZMod n) (ZMod n)
  let : Injective (ModuleCat.of (ZMod n) (ULift.{max c h} (ZMod n))) := inferInstance
  exact ModuleCat.Sheaf.locallyBoundary_finite_of_constantInjective J I N _ η i hi hN hI M q

/-- info: 'ModuleCat.Sheaf.boundarySieve' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.boundarySieve

/-- info: 'ModuleCat.Sheaf.LocallyBoundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.LocallyBoundary

/-- info: 'ModuleCat.Sheaf.locallyBoundary_of_projective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.locallyBoundary_of_projective

/-- info: 'ModuleCat.Sheaf.locallyBoundary_of_syzygy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.locallyBoundary_of_syzygy

/-- info: 'ModuleCat.Sheaf.locallyBoundary_zero_of_presentation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.locallyBoundary_zero_of_presentation

/-- info: 'ModuleCat.Sheaf.locallyBoundary_finite_of_constantInjective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.locallyBoundary_finite_of_constantInjective
