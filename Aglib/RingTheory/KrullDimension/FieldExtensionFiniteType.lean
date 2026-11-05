/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.KrullDimension.IntegralExtension
public import Aglib.Topology.KrullDimension.Surjective
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Dimension of finite-type algebras after extending the ground field

An actual finite Noether normalization bounds the dimension after an arbitrary
field extension by the original dimension. The original integral
prime-spectrum map is a closed surjection; dimension descent does not require
the original algebra to be a domain, reduced, or normal. The tensor product is allowed to acquire
zero divisors or nilpotents. All three ring universes are independent.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra

universe u v w

/-- Extending the ground field does not increase the Krull dimension of a
nontrivial finite-type algebra. The ground field need not be algebraically closed or
perfect, and the extension field need not be algebraic. -/
theorem ringKrullDim_tensorProduct_le_of_finiteType
    (k : Type u) [Field k] (A : Type v) [CommRing A] [Nontrivial A]
    [Algebra k A] [FiniteType k A] (K : Type w) [Field K] [Algebra k K] :
    ringKrullDim (K ⊗[k] A) ≤ ringKrullDim A := by
  obtain ⟨n, g, hg, hfinite⟩ := exists_finite_inj_algHom_of_fg k A
  let : Algebra (MvPolynomial (Fin n) k) A := g.toRingHom.toAlgebra
  let : Module.Finite (MvPolynomial (Fin n) k) A := hfinite
  let : FaithfulSMul (MvPolynomial (Fin n) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  have hn : (n : WithBot ℕ∞) ≤ ringKrullDim A := by
    have hdim : ringKrullDim (MvPolynomial (Fin n) k) ≤ ringKrullDim A := by
      simpa only [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] using
        TopologicalSpace.topologicalKrullDim_le_of_isClosedMap_of_surjective
          (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) k) A))
          (PrimeSpectrum.continuous_comap _)
          (PrimeSpectrum.isClosedMap_comap_of_isIntegral _
            (by intro x; exact Algebra.IsIntegral.isIntegral x))
          (Algebra.IsIntegral.comap_surjective (MvPolynomial (Fin n) k) A)
    simpa only [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field, zero_add, Nat.card_fin] using hdim
  let ψ : K ⊗[k] MvPolynomial (Fin n) k →ₐ[k] K ⊗[k] A :=
    TensorProduct.map (AlgHom.id k K) g
  have hψ : ψ.toRingHom.Finite :=
    RingHom.Finite.tensorProductMap (f := AlgHom.id k K) (g := g)
      (RingHom.Finite.id K) hfinite
  let θ : MvPolynomial (Fin n) K →+* K ⊗[k] A :=
    ψ.toRingHom.comp (MvPolynomial.algebraTensorAlgEquiv k K).symm.toRingEquiv.toRingHom
  have hθ : θ.Finite := hψ.comp (RingEquiv.finite _)
  let : Algebra (MvPolynomial (Fin n) K) (K ⊗[k] A) := θ.toAlgebra
  let : Module.Finite (MvPolynomial (Fin n) K) (K ⊗[k] A) := hθ
  calc
    ringKrullDim (K ⊗[k] A) ≤ ringKrullDim (MvPolynomial (Fin n) K) := by
      apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap θ)
      intro P Q hPQ
      exact Ideal.IsIntegral.under_lt_under hPQ
    _ = (n : WithBot ℕ∞) := by
      simp only [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
        ringKrullDim_eq_zero_of_field, zero_add, Nat.card_fin]
    _ ≤ ringKrullDim A := hn

end Algebra
