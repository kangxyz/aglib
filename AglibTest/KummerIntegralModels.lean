/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Kummer.Valuation

/-! Native clients of the actual polynomial quotient, signed valuations and integral closure. -/

@[expose] public section

open Algebra.Kummer Polynomial UniqueFactorizationMonoid
open scoped TensorProduct

/-- The arbitrary-parameter root algebra also covers nonunits with nilpotent roots. -/
example : Module.Finite ℤ (AdjoinRoot (X ^ 2 - C (0 : ℤ))) :=
  root_finite 2 (by decide) 0

/-- Scaling is an algebra isomorphism at level zero as well; no etale statement is used. -/
example (K : Type*) [Field K] (u g : K) (hg : g ≠ 0) :
    scaleEquiv 0 u u g hg (by simp) (AdjoinRoot.root (rootPolynomial 0 u)) =
      algebraMap K (RootAlgebra 0 u) g⁻¹ * AdjoinRoot.root (rootPolynomial 0 u) :=
  scaleEquiv_root 0 u u g hg (by simp)

section Factorization

variable {R K : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
  [NormalizationMonoid R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- The proved UFD decomposition feeds the same literal tensor/root scaling map. -/
example (n : ℕ) (f : K) (hf : FactorizationDivisible (R := R) n f) :
    ∃ (u : Rˣ) (g : K) (hg : g ≠ 0) (hfg : f = algebraMap R K (u : R) * g ^ n),
      genericModelEquiv n (u : R) f g hg hfg
          (1 ⊗ₜ[R] AdjoinRoot.root (rootPolynomial n (u : R))) =
        algebraMap K (RootAlgebra n f) g⁻¹ * AdjoinRoot.root (rootPolynomial n f) := by
  obtain ⟨u, g, hg, hfg⟩ := unit_mul_power n f hf
  exact ⟨u, g, hg, hfg, genericModelEquiv_root n (u : R) f g hg hfg⟩

variable [IsNoetherianRing R]

/-- The normalized integer order detects the simple pole of an actual prime inverse. -/
example {p : R} (hp : Prime p) :
    let : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
    heightOneOrder (K := K) (Ideal.span {p}) (height_span_prime hp)
      (algebraMap R K p)⁻¹ = -1 := by
  classical
  let : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have hfin : FiniteMultiplicity p p := finiteMultiplicity_of_emultiplicity_eq_natCast
    (emultiplicity_eq_count_normalizedFactors hp.irreducible hp.ne_zero)
  have horder := heightOneOrder_span_div_multiplicity (K := K) hp one_ne_zero hp.ne_zero
  simpa only [map_one, one_div, multiplicity_one_right, multiplicity_self hfin,
    Nat.cast_zero, Nat.cast_one, zero_sub] using horder

end Factorization

section LiteralClosure

universe u
variable {R K : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] [UniqueFactorizationMonoid R] [NormalizationMonoid R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- All-height-one divisibility gives the literal normalization, retaining the
positive invertible level and the exact supplied field parameter. -/
example (n : ℕ) (hn : 0 < n) (hnR : IsUnit (n : R)) (f : K) (hf : f ≠ 0)
    (hdiv : ∀ (P : Ideal R) [P.IsPrime] (hP : P.height = 1),
      (n : ℤ) ∣ heightOneOrder (K := K) P hP f) :
    Module.Finite R (integralClosure R (AdjoinRoot (X ^ n - C f))) ∧
      Algebra.Etale R (integralClosure R (AdjoinRoot (X ^ n - C f))) :=
  finite_etale_integralClosure_of_heightOneOrder n hn hnR f hf hdiv

end LiteralClosure
