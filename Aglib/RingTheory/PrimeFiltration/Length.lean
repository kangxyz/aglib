/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.PrimeFiltration.Primes
public import Mathlib.RingTheory.Length

/-!
# Length along actual prime filtrations

Extended-natural length is additive on nested submodule quotients and along a given finite prime
filtration. The formulas allow infinite length and use actual quotient equivalences.

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

theorem length_add_of_submodule_le (U V : Submodule A M) (hUV : U ≤ V) :
    Module.length A V = Module.length A U + Module.length A (V ⧸ U.comap V.subtype) := by
  let C : Submodule A V := U.comap V.subtype
  let f : U →ₗ[A] V := Submodule.inclusion hUV
  have hex : Function.Exact f C.mkQ := by
    intro x
    constructor
    · intro hx
      have hm : (x : M) ∈ U := (Submodule.Quotient.mk_eq_zero C).mp hx
      exact ⟨⟨x, hm⟩, Subtype.ext rfl⟩
    · rintro ⟨y, rfl⟩
      apply (Submodule.Quotient.mk_eq_zero C).mpr
      exact y.property
  exact Module.length_eq_add_of_exact f C.mkQ (Submodule.inclusion_injective hUV)
    (Submodule.mkQ_surjective C) hex

namespace PrimeFiltrationFrom

theorem length_eq_add_sum {U : Submodule A M} (D : PrimeFiltrationFrom M U) :
    Module.length A M = Module.length A U +
      (D.primes.map fun p => Module.length A (A ⧸ p)).sum := by
  induction D with
  | top =>
    simpa only [primes, List.map_nil, List.sum_nil, add_zero] using
      (Submodule.topEquiv (R := A) (M := M)).length_eq.symm
  | @step U V hUV p hp e tail ih =>
    have hstep := length_add_of_submodule_le U V hUV.le
    rw [e.length_eq] at hstep
    rw [hstep] at ih
    simpa only [primes, List.map_cons, List.sum_cons, add_assoc] using ih

end PrimeFiltrationFrom
end Module
