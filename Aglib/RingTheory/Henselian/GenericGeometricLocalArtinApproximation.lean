/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.GeometricLocalArtinApproximation
public import Aglib.RingTheory.Localization.FractionBase

/-!
# Artin approximation above the generic point of a domain

A prime with zero base contraction is localized along the actual nonzero base
elements. The already proved field theorem applies over the actual fraction
field. The literal localization and henselization equivalences transport its
solution and precision back to the original ideal completion. The original
finite-type algebra is not assumed to be a domain or flat.
-/

@[expose] public section

noncomputable section

open MvPolynomial

universe u v w t

namespace GenericGeometricLocalHenselization

variable (R : Type u) [CommRing R] [IsDomain R]
variable (B : Type v) [CommRing B] [Algebra R B]
variable [Algebra.FiniteType R B] (q : Ideal B) [q.IsPrime]

include R in
/-- Geometric Artin approximation with precision in the original ideal and completion. -/
theorem exists_solution_ideal_completion_with_precision
    (hq : q.comap (algebraMap R B) = ⊥)
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
  let B' := FractionBaseLocalization.BaseLocalized R B
  let q' := FractionBaseLocalization.selectedPrime R B q
  let : q'.IsPrime := FractionBaseLocalization.selectedPrime_isPrime R B q hq
  let : Algebra.FiniteType (FractionRing R) B' := FractionBaseLocalization.finiteType R B R
  let e := (Henselization.equivOfRingEquiv
    (FractionBaseLocalization.localEquiv R B q hq).toRingEquiv).symm
  have hJ : I.map e.toRingHom ≠ ⊤ := AdicCompletion.map_ne_top_of_ringEquiv e I hI
  refine AdicCompletion.exists_solution_of_ringEquiv_solver e I ?_ F y hy c
  intro E s hs d
  exact GeometricLocalHenselization.exists_solution_ideal_completion_with_precision
    (FractionRing R) B' q' (I.map e.toRingHom) hJ E s hs d

end GenericGeometricLocalHenselization
