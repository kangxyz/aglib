/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Smooth.Locus

/-! # Smoothness at corresponding primes under an algebra equivalence

The native localization equivalence is formed over abstract coefficient and
source rings. Its two prime complements are the actual corresponding submonoids;
no localization, coefficient action, or smoothness supplier is replaced.
-/

@[expose] public noncomputable section

namespace Algebra

universe u v w

variable {R : Type u} {A : Type v} {B : Type w}
  [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Smoothness at a prime transports to its actual inverse image under the
supplied coefficient-compatible algebra equivalence. -/
theorem IsSmoothAt.of_algEquiv (e : A ≃ₐ[R] B) (q : Ideal B) [q.IsPrime]
    (hq : IsSmoothAt R q) : IsSmoothAt R (q.comap e.toRingEquiv) := by
  let qA : Ideal A := q.comap e.toRingEquiv
  let : qA.IsPrime := Ideal.comap_isPrime e.toRingEquiv q
  have hprimeCompl : Submonoid.map e qA.primeCompl = q.primeCompl := by
    change Submonoid.map e.toRingEquiv (q.comap e.toRingEquiv).primeCompl = q.primeCompl
    exact e.toRingEquiv.map_primeCompl_comap_eq q
  let eLocal : Localization.AtPrime qA ≃ₐ[R] Localization.AtPrime q :=
    IsLocalization.algEquivOfAlgEquiv (A := R) (R := A) (P := B)
      (M := qA.primeCompl) (T := q.primeCompl)
      (Localization.AtPrime qA) (Localization.AtPrime q) e hprimeCompl
  exact (Algebra.FormallySmooth.iff_of_equiv eLocal).mpr hq

end Algebra
