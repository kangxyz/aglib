/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.StrictHenselization.FiniteLocalFactors
public import Aglib.RingTheory.FiniteLength.FiniteAlgebraFiber
public import Mathlib.RingTheory.Spectrum.Maximal.Localization

/-!
# The canonical finite local decomposition over a Henselian ring

The original algebra map to the product of its maximal localizations is an
isomorphism. The projection to every factor is the literal localization map.
The index is finite by the closed-fibre finiteness theorem, not by an Artinian
assumption on the algebra itself.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped BigOperators

universe u v

namespace HenselianLocalRing

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A]

include R in
/-- The native maximal-localization map of a finite Henselian-base algebra is
surjective because that selected localization is an idempotent quotient. -/
theorem algebraMap_localizationAtPrime_surjective (q : Ideal A) [q.IsMaximal] :
    Function.Surjective (algebraMap A (Localization.AtPrime q)) := by
  obtain ⟨e, he, heq, hi⟩ := exists_idempotent_isolating_maximal R A q
  let E := IsLocalization.quotientEquivAtPrimeOfIsolatingIdempotent q e he heq hi
  intro z
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (E.symm z)
  refine ⟨a, ?_⟩
  calc
    algebraMap A (Localization.AtPrime q) a = E (Ideal.Quotient.mk _ a) :=
      (E.commutes a).symm
    _ = z := by rw [ha]; exact E.apply_symm_apply z

/-- An isolating idempotent has the Kronecker projection values in the actual
maximal localizations. -/
theorem localization_isolating_idempotent [DecidableEq (MaximalSpectrum A)]
    (p q : MaximalSpectrum A) (e : A) (he : IsIdempotentElem e)
    (hep : e ∉ p.asIdeal)
    (hi : ∀ P : Ideal A, P.IsMaximal → e ∉ P → P = p.asIdeal) :
    algebraMap A (Localization.AtPrime q.asIdeal) e = if q = p then 1 else 0 := by
  classical
  by_cases hqp : q = p
  · subst q
    rw [ite_eq_left rfl]
    exact (IsIdempotentElem.iff_eq_one_of_isUnit
      (IsLocalization.map_units (Localization.AtPrime p.asIdeal)
        (⟨e, hep⟩ : p.asIdeal.primeCompl))).mp (he.map _)
  · rw [ite_eq_right hqp]
    have heq : e ∈ q.asIdeal := by
      by_contra hn
      exact hqp (MaximalSpectrum.ext (hi q.asIdeal q.isMaximal hn))
    have hneq : 1 - e ∉ q.asIdeal := by
      intro h
      apply q.isMaximal.isPrime.one_notMem
      have h' := q.asIdeal.add_mem h heq
      simpa using h'
    have hu := IsLocalization.map_units (Localization.AtPrime q.asIdeal)
      (⟨1 - e, hneq⟩ : q.asIdeal.primeCompl)
    apply hu.mul_left_cancel
    rw [mul_zero, ← map_mul, he.one_sub_mul_self, map_zero]

include R in
/-- The canonical map to all maximal localizations is bijective for a finite
algebra over a Henselian local ring. -/
theorem toPiLocalization_bijective :
    Function.Bijective (MaximalSpectrum.toPiLocalization A) := by
  classical
  let : Finite (MaximalSpectrum A) := Module.finiteAlgebra_maximalSpectrum_finite R A
  let : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  refine ⟨MaximalSpectrum.toPiLocalization_injective A, ?_⟩
  intro z
  choose e he hep hi using fun p : MaximalSpectrum A =>
    exists_idempotent_isolating_maximal R A p.asIdeal
  choose a ha using fun p : MaximalSpectrum A =>
    algebraMap_localizationAtPrime_surjective R A p.asIdeal (z p)
  refine ⟨∑ p, e p * a p, ?_⟩
  funext q
  change algebraMap A (Localization.AtPrime q.asIdeal) (∑ p, e p * a p) = z q
  rw [map_sum]
  simp_rw [map_mul, localization_isolating_idempotent A _ _ _ (he _) (hep _) (hi _)]
  simp [ha]

/-- Canonical product decomposition, with maximal localizations as the factors. -/
def finiteAlgebraLocalDecomposition : A ≃ₐ[A] MaximalSpectrum.PiLocalization A :=
  AlgEquiv.ofBijective (MaximalSpectrum.toPiLocalization A) (toPiLocalization_bijective R A)

/-- Each component of the decomposition is the original localization map. -/
@[simp] theorem finiteAlgebraLocalDecomposition_apply (a : A) (q : MaximalSpectrum A) :
    finiteAlgebraLocalDecomposition R A a q =
      algebraMap A (Localization.AtPrime q.asIdeal) a := rfl

end HenselianLocalRing
