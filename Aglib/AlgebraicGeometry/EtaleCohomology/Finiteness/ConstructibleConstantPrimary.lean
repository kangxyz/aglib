/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ConstructibleCyclicPrimary

/-! # Constructible higher images of original finite primary constant groups

Native cyclic decomposition reduces a finite underlying abelian group to the
positive cyclic divisors of its given annihilator. The original constant-sheaf
functor and original higher images retain the original coefficient throughout.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

/-- For a proper morphism over a locally Noetherian characteristic-p base,
each higher image of the original finite abelian constant group killed by a
power of p is constructible. Finiteness means finite underlying group, not
finite generation over an auxiliary ring. -/
theorem constantPrimaryHigherDirectImage_isConstructible
    {X S : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S) [IsProper f]
    (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0)
    (A : Type u) [AddCommGroup A] [Finite A] (r : ℕ)
    (hA : ∀ a : A, (p ^ r) • a = 0) (q : ℕ) :
    Constructible.IsConstructible
      ((higherDirectImage f q).obj (ConstantFinite.coefficient A X)) := by
  apply constantHigherDirectImage_isConstructible_of_cyclic_divisors f (p ^ r) _ A hA q
  intro m _ hm n
  obtain ⟨s, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hm
  exact cyclicPrimePowerHigherDirectImage_isConstructible f p hp hS s n

end AlgebraicGeometry.Scheme.EtaleCohomology
