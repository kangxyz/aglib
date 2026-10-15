/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Ideal.Height

/-!
# Heights under integral extensions with going down

Integral extensions with going down preserve the height of every prime ideal under canonical
contraction. A further interface obtains going down from a normal base and a faithful integral
domain extension. No finite-dimensionality hypothesis is imposed.

## Extraction basis

Transferred from `R5Lab.RingTheory.KrullDimension.IntegralGoingDown` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`4204b2004922b41c66cd30b9bc30cba3af3f825a33c80500d863df85d8c830ae`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Integral incomparability and going down preserve the height of every prime.
No finiteness or dimension assumption is used. -/
theorem _root_.PrimeSpectrum.primeSpectrum_height_comap
    [Algebra.IsIntegral R S] [Algebra.HasGoingDown R S]
    (Q : PrimeSpectrum S) :
    Order.height Q = Order.height (PrimeSpectrum.comap (algebraMap R S) Q) := by
  apply Order.height_eq_of_strictMono
    (PrimeSpectrum.comap (algebraMap R S))
  · intro P Q hPQ
    exact Ideal.IsIntegral.under_lt_under hPQ
  · intro Q p hpQ
    obtain ⟨P, hPQ, hP, hPp⟩ :=
      Ideal.exists_ideal_lt_liesOver_of_lt (R := R) Q.asIdeal hpQ
    exact ⟨⟨P, hP⟩, hPQ, PrimeSpectrum.ext hPp.over.symm⟩

/-- The ideal-height version of integral incomparability plus going down. -/
theorem height_eq_height_under [Algebra.IsIntegral R S] [Algebra.HasGoingDown R S]
    (Q : Ideal S) [Q.IsPrime] : Q.height = (Q.under R).height := by
  simpa only [← PrimeSpectrum.height_eq_orderHeight, PrimeSpectrum.comap_asIdeal,
    Ideal.under_def] using
    PrimeSpectrum.primeSpectrum_height_comap (R := R) (S := S) ⟨Q, inferInstance⟩

/-- Every prime of an integral domain extension over a normal base has the
same height as its contraction. -/
theorem height_eq_height_under_of_normal [IsDomain S] [FaithfulSMul R S]
    [Algebra.IsIntegral R S] [IsIntegrallyClosed R]
    (Q : Ideal S) [Q.IsPrime] : Q.height = (Q.under R).height :=
  height_eq_height_under Q

end Ideal
