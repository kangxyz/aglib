/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.GeometricLocalFiniteOriginModel
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationFiniteLocalApproximation
public import Aglib.RingTheory.AdicCompletion.RingEquivApproximation

/-!
# Artin approximation for geometric local henselizations

For an arbitrary field and an arbitrary prime of a finite-type algebra, the
actual henselization of the prime localization admits approximation in the
completion at every proper ideal. The actual finite-origin model and the proved
finite-local solver are combined using the actual cross-universe completion
equivalence. Both literal quotient precision and original completion ideal-power
error are retained. No approximation or reduction-model premise remains.
-/

@[expose] public section

noncomputable section

open MvPolynomial

universe u v w t

namespace GeometricLocalHenselization

variable (k : Type u) [Field k] (B : Type v) [CommRing B] [Algebra k B]
variable [Algebra.FiniteType k B] (q : Ideal B) [q.IsPrime]

include k in
/-- Geometric Artin approximation with precision in the original ideal and completion. -/
theorem exists_solution_ideal_completion_with_precision
    (I : Ideal (Henselization (Localization.AtPrime q))) (hI : I ≠ ⊤)
    {σ : Type w} {ι : Type t} [Finite σ] [Finite ι]
    (F : ι → MvPolynomial σ (Henselization (Localization.AtPrime q)))
    (y : σ → AdicCompletion I (Henselization (Localization.AtPrime q)))
    (hy : ∀ i, eval₂
      (algebraMap (Henselization (Localization.AtPrime q))
        (AdicCompletion I (Henselization (Localization.AtPrime q)))) y (F i) = 0)
    (c : ℕ) :
    ∃ x : σ → Henselization (Localization.AtPrime q),
      (∀ i, eval x (F i) = 0) ∧
      (∀ j, Ideal.Quotient.mk (I ^ c) (x j) = AdicCompletion.evalₐ I c (y j)) ∧
      ∀ j, algebraMap (Henselization (Localization.AtPrime q))
        (AdicCompletion I (Henselization (Localization.AtPrime q))) (x j) - y j ∈
        (I ^ c).map (algebraMap (Henselization (Localization.AtPrime q))
          (AdicCompletion I (Henselization (Localization.AtPrime q)))) := by
  obtain ⟨K, hK, n, A, hA, aA, fA, lA, ⟨e⟩⟩ := exists_finite_origin_model k B q
  let := hK
  let := hA
  let := aA
  let := fA
  let := lA
  have hJ : I.map e.toRingHom ≠ ⊤ := AdicCompletion.map_ne_top_of_ringEquiv e I hI
  refine AdicCompletion.exists_solution_of_ringEquiv_solver e I ?_ F y hy c
  intro E s hs d
  exact PolynomialLocalHenselization.exists_solution_finite_local_ideal_completion_with_precision
    K n A (I.map e.toRingHom) hJ E s hs d

end GeometricLocalHenselization
