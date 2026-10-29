/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Smooth.ArtinianLifting

/-!
# Consumer checks for the Artinian-test criterion for formal smoothness

The criterion `Algebra.FormallySmooth.of_lift_artinianLocal_squareZero` for a presentation by a
Noetherian local formally smooth algebra with finite free differentials, its form
`Algebra.FormallySmooth.of_lift_artinianLocal_squareZero_of_isLocalization` for a localization of
a finite type algebra over a Noetherian ring (here at `Localization.AtPrime`), and the test-ring
facts; axiom guards.
-/

@[expose] public section

noncomputable section

open IsLocalRing KaehlerDifferential

universe u v

namespace AglibTest.ArtinianLifting

/-- The criterion for a presentation `P → S`. -/
example {R S : Type*} {P : Type v} [CommRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
    [CommRing P] [IsLocalRing P] [IsNoetherianRing P] [Algebra R P] [Algebra P S]
    [IsScalarTower R P S] [Algebra.FormallySmooth R P]
    [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]]
    (hsurj : Function.Surjective (algebraMap P S))
    (H : ∀ (A' A : Type v) [CommRing A'] [CommRing A] [IsLocalRing A'] [IsArtinianRing A']
      [Algebra R A'] [Algebra R A] (g : A' →ₐ[R] A), Function.Surjective g →
      RingHom.ker g ^ 2 = ⊥ → ∀ φ : S →ₐ[R] A, Function.Surjective φ →
        ∃ ψ : S →ₐ[R] A', g.comp ψ = φ) :
    Algebra.FormallySmooth R S :=
  Algebra.FormallySmooth.of_lift_artinianLocal_squareZero hsurj H

/-- The criterion at a prime of a finite type algebra over a Noetherian ring, for the native
`Localization.AtPrime`. -/
example {R : Type u} {B : Type*} [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B]
    [Algebra.FiniteType R B] (q : Ideal B) [q.IsPrime]
    (H : ∀ (A' A : Type u) [CommRing A'] [CommRing A] [IsLocalRing A'] [IsArtinianRing A']
      [Algebra R A'] [Algebra R A] (g : A' →ₐ[R] A), Function.Surjective g →
      RingHom.ker g ^ 2 = ⊥ → ∀ φ : Localization.AtPrime q →ₐ[R] A, Function.Surjective φ →
        ∃ ψ : Localization.AtPrime q →ₐ[R] A', g.comp ψ = φ) :
    Algebra.FormallySmooth R (Localization.AtPrime q) :=
  Algebra.FormallySmooth.of_lift_artinianLocal_squareZero_of_isLocalization q H

/-- The single test extension `P ⧸ 𝔪 * J → P ⧸ J` is Artinian local with square-zero kernel. -/
example {R P : Type*} [CommRing R] [CommRing P] [IsLocalRing P] [IsNoetherianRing P]
    [Algebra R P] {J : Ideal P} {m : ℕ} (hJm : maximalIdeal P ^ m ≤ J)
    (hJ : J ≤ maximalIdeal P) :
    IsLocalRing (P ⧸ maximalIdeal P * J) ∧ IsArtinianRing (P ⧸ maximalIdeal P * J) ∧
      RingHom.ker (Ideal.Quotient.factorₐ R
        (Ideal.mul_le_right : maximalIdeal P * J ≤ J)) ^ 2 = ⊥ :=
  ⟨IsLocalRing.isLocalRing_quotient_maximalIdeal_mul J,
    IsLocalRing.isArtinianRing_quotient_maximalIdeal_mul hJm,
    Ideal.Quotient.ker_factorₐ_mul_sq_eq_bot hJ⟩

end AglibTest.ArtinianLifting

/--
info: 'Ideal.Quotient.mk_mul_eq_zero_of_mem_ker_factorₐ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ideal.Quotient.mk_mul_eq_zero_of_mem_ker_factorₐ

/--
info: 'Ideal.Quotient.ker_factorₐ_mul_sq_eq_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ideal.Quotient.ker_factorₐ_mul_sq_eq_bot

/--
info: 'IsLocalRing.isLocalRing_quotient_maximalIdeal_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsLocalRing.isLocalRing_quotient_maximalIdeal_mul

/--
info: 'IsLocalRing.isArtinianRing_quotient_maximalIdeal_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsLocalRing.isArtinianRing_quotient_maximalIdeal_mul

/--
info: 'Algebra.FormallySmooth.lift_eq_mk_of_D_mem_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Algebra.FormallySmooth.lift_eq_mk_of_D_mem_smul

/--
info: 'Algebra.FormallySmooth.of_lift_artinianLocal_squareZero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Algebra.FormallySmooth.of_lift_artinianLocal_squareZero

/--
info: 'Algebra.FormallySmooth.of_lift_artinianLocal_squareZero_of_isLocalization' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Algebra.FormallySmooth.of_lift_artinianLocal_squareZero_of_isLocalization
