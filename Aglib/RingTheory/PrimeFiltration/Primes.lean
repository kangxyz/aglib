/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/

module

public import Aglib.RingTheory.PrimeFiltration.Basic

/-!
# The prime factors of an actual filtration

The recursive list records the actual prime cyclic quotients of a finite filtration. Its
definition requires neither a length equality nor an Euler premise.

## Extraction basis

Transferred subsets of `R5Lab.RingTheory.LocalLength.PrincipalEulerFiltration` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, source SHA-256
`860f378ac24bc0033903038bcae32ff592ede183c1c0378541bfd5a3a092a1f6`. Objects, universes,
canonical maps and
actual premises are retained; declarations use native mathematical namespaces.
-/

@[expose] public section

noncomputable section

namespace Module
universe u v
variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

namespace PrimeFiltrationFrom

/-- The ordered list of prime ideals recorded by the steps of the supplied prime filtration. -/
def primes {U : Submodule A M} (D : PrimeFiltrationFrom M U) : List (Ideal A) :=
  match D with
  | top => []
  | step _ p _ _ tail => p :: primes tail

end PrimeFiltrationFrom
end Module
