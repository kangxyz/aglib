/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field

/-! # Noether normalization in dimension at most one

Integral injected subrings of a one-dimensional domain also have dimension at
most one, by lying over and contraction of maximal ideals. The native Noether
normalization therefore needs at most one variable. No perfection or separable
generation hypothesis is used.
-/

@[expose] public noncomputable section

namespace Algebra

/-- Dimension at most one descends through an integral injection of domains. -/
theorem krullDimLE_one_of_integral_injective
    (R S : Type*) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [Algebra.IsIntegral R S] [FaithfulSMul R S]
    [Ring.KrullDimLE 1 S] : Ring.KrullDimLE 1 R := by
  apply Ring.krullDimLE_one_iff_of_isPrime_bot.mpr
  intro P hP hprime
  let : P.IsPrime := hprime
  obtain ⟨Q, _, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    P (⊥ : Ideal S) (by
      change Ideal.comap (algebraMap R S) ⊥ ≤ P
      rw [Ideal.comap_bot_of_injective (algebraMap R S)
        (FaithfulSMul.algebraMap_injective R S)]
      exact bot_le)
  let : Q.IsPrime := hQ
  have hQne : Q ≠ ⊥ := by
    intro h
    apply hP
    rw [← hQP, h]
    exact Ideal.comap_bot_of_injective (algebraMap R S)
      (FaithfulSMul.algebraMap_injective R S)
  let : Q.IsMaximal := (Ring.krullDimLE_one_iff_of_isPrime_bot.mp
    (inferInstance : Ring.KrullDimLE 1 S)) Q hQne hQ
  have hm := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) Q
  rwa [hQP] at hm

end Algebra

namespace NoetherNormalization

/-- A finite-type domain of dimension at most one has an actual integral
normalization by a polynomial algebra in zero or one variables. -/
theorem exists_integral_inj_algHom_dim_le_one
    (k A : Type*) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (hdim : ringKrullDim A ≤ 1) :
    ∃ n ≤ 1, ∃ g : MvPolynomial (Fin n) k →ₐ[k] A,
      Function.Injective g ∧ g.IsIntegral := by
  obtain ⟨n, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k A
  let : Algebra (MvPolynomial (Fin n) k) A := g.toRingHom.toAlgebra
  let : Algebra.IsIntegral (MvPolynomial (Fin n) k) A := ⟨hint⟩
  let : FaithfulSMul (MvPolynomial (Fin n) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  let : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr hdim
  have hn := Ring.krullDimLE_iff.mp
    (Algebra.krullDimLE_one_of_integral_injective (MvPolynomial (Fin n) k) A)
  simp only [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, zero_add, Nat.card_fin] at hn
  refine ⟨n, ?_, g, hg, hint⟩
  exact_mod_cast hn

end NoetherNormalization
