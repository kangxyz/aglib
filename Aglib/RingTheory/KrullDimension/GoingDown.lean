/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.Height

/-! # Heights under the original going-down map

Lifting every prime chain ending at the original contracted prime proves the
height inequality. Integrality, finiteness and Noetherianity are not needed.
-/

@[expose] public section

namespace PrimeSpectrum

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Going down bounds the height of the original contracted prime. -/
theorem height_comap_le_of_hasGoingDown [Algebra.HasGoingDown R S] (q : PrimeSpectrum S) :
    Order.height (comap (algebraMap R S) q) ≤ Order.height q := by
  apply Order.height_le_iff'.mpr
  intro l hl
  let : q.asIdeal.LiesOver l.last.asIdeal := by
    rw [hl]
    infer_instance
  obtain ⟨L, hlen, hlast, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l q.asIdeal
  have h := Order.length_le_height_last (p := L)
  rw [hlen, hlast] at h
  exact h

end PrimeSpectrum

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Ideal heights have the same going-down bound, with the original contraction. -/
theorem height_under_le_of_hasGoingDown [Algebra.HasGoingDown R S]
    (q : Ideal S) [q.IsPrime] : (q.under R).height ≤ q.height := by
  simpa only [← PrimeSpectrum.height_eq_orderHeight, PrimeSpectrum.comap_asIdeal,
    under_def] using PrimeSpectrum.height_comap_le_of_hasGoingDown (R := R) (S := S)
      ⟨q, inferInstance⟩

end Ideal
