/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.PrimePowerReduction
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Finite constant reduction bounded by an actual annihilator

The original finite direct-sum factors are quotients of the original group.
Native exponent divisibility proves that each factor order divides the given
annihilator. The shared original split-family construction therefore requires
comparison only for positive cyclic divisors of that annihilator, not for
unrelated characteristic-primary coefficients.
-/

@[expose] public noncomputable section

universe u w w'

open CategoryTheory
open scoped DirectSum

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : S ⟶ X)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- Only positive cyclic divisors of an actual annihilator are needed for
surjectivity of the original finite constant coefficient restriction. -/
theorem constantRestriction_surjective_of_cyclic_divisors (q : ℕ) (N : ℕ)
    (h : ∀ m : ℕ, 0 < m → m ∣ N →
      Function.Surjective (constantRestriction (ULift.{u} (ZMod m)) f q))
    (A : Type u) [AddCommGroup A] [Finite A] (hN : ∀ a : A, N • a = 0) :
    Function.Surjective (constantRestriction A f q) := by
  classical
  obtain ⟨ι, hι, p, hp, r, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite A
  let := hι
  apply constantRestriction_surjective_of_zmod_directSum_equiv f q (fun i => p i ^ r i) e
  intro i
  have hs : Function.Surjective
      ((DFinsupp.evalAddMonoidHom i).comp e.toAddMonoidHom) := by
    intro a
    refine ⟨e.symm (DirectSum.of (fun j => ZMod (p j ^ r j)) i a), ?_⟩
    change (e (e.symm (DirectSum.of (fun j => ZMod (p j ^ r j)) i a))) i = a
    rw [e.apply_symm_apply]
    exact DirectSum.of_eq_same (β := fun j => ZMod (p j ^ r j)) i a
  have he : AddMonoid.exponent A ∣ N :=
    AddMonoid.exponent_dvd_iff_forall_nsmul_eq_zero.mpr hN
  have hd : p i ^ r i ∣ N := by
    rw [← ZMod.exponent (p i ^ r i)]
    exact (AddMonoidHom.exponent_dvd hs).trans he
  exact h (p i ^ r i) (pow_pos (hp i).pos _) hd

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
