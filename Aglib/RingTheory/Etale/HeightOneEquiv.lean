/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.RingTheory.Ideal.Height

/-! Transport of source-codimension-one unramifiedness along the original algebra equivalence. -/

@[expose] public section

namespace Algebra

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]

/-- An algebra equivalence preserves unramifiedness at all height-one source primes. -/
theorem unramified_height_one_of_equiv (e : B ≃ₐ[A] C)
    (h : ∀ q : PrimeSpectrum B, q.asIdeal.height = 1 → IsUnramifiedAt A q.asIdeal) :
    ∀ q : PrimeSpectrum C, q.asIdeal.height = 1 → IsUnramifiedAt A q.asIdeal := by
  intro q hq
  let p : PrimeSpectrum B := PrimeSpectrum.comap e.toRingHom q
  have hp : p.asIdeal.height = 1 := by
    change (q.asIdeal.comap e.toRingHom).height = 1
    exact (e.toRingEquiv.height_comap q.asIdeal).trans hq
  let : IsUnramifiedAt A p.asIdeal := h p hp
  exact FormallyUnramified.of_equiv (Localization.localAlgEquiv p.asIdeal q.asIdeal e rfl)

end Algebra
