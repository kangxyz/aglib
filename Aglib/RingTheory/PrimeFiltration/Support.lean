/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/

module

public import Aglib.RingTheory.PrimeFiltration.Primes
public import Mathlib.RingTheory.Support

/-!
# Support of the actual prime factors

Every recorded factor prime is prime and its quotient support is contained in the original
module support. These results concern the given filtration and do not assume scalar homology
finiteness.

## Extraction basis

Transferred subsets of `R5Lab.RingTheory.LocalLength.PrincipalEulerSupport` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, source SHA-256
`5dd0cee73230a6d3cf58f6ac525d8aa880a5bc6e7ad08eb823b6f0e2913099eb`. Objects, universes,
canonical maps and
actual premises are retained; declarations use native mathematical namespaces.
-/

@[expose] public section

noncomputable section

namespace Module
universe u v
variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

namespace PrimeFiltrationFrom

theorem primes_isPrime {U : Submodule A M} (D : PrimeFiltrationFrom M U)
    (p : Ideal A) (hp : p ∈ D.primes) : p.IsPrime := by
  induction D with
  | top => simp [primes] at hp
  | step _ q hq _ _ ih =>
    simp only [primes, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hq
    · exact ih hp

/-- Every literal filtration factor has support contained in the original
module's support. In particular, its prime belongs to that support. -/
theorem prime_mem_support {U : Submodule A M} (D : PrimeFiltrationFrom M U)
    (p : Ideal A) (hp : p ∈ D.primes) :
    (⟨p, D.primes_isPrime p hp⟩ : PrimeSpectrum A) ∈ Module.support A M := by
  induction D with
  | top => simp [primes] at hp
  | @step U V hUV q hq e tail ih =>
    simp only [primes, List.mem_cons] at hp
    rcases hp with rfl | hp
    · let q' : PrimeSpectrum A := ⟨p, hq⟩
      have hs : q' ∈ Module.support A (A ⧸ p) := by
        rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
        change p ≤ p
        exact le_rfl
      rw [← e.support_eq] at hs
      exact (Module.support_subset_of_injective V.subtype (Submodule.subtype_injective V))
        ((Module.support_subset_of_surjective _ (Submodule.mkQ_surjective _)) hs)
    · exact ih hp

theorem primeFactor_support_subset {U : Submodule A M} (D : PrimeFiltrationFrom M U)
    (p : Ideal A) (hp : p ∈ D.primes) :
    Module.support A (A ⧸ p) ⊆ Module.support A M := by
  intro q hq
  have hle : p ≤ q.asIdeal := by
    simpa only [Ideal.annihilator_quotient] using Module.annihilator_le_of_mem_support hq
  exact Module.mem_support_mono hle (D.prime_mem_support p hp)

end PrimeFiltrationFrom
end Module
