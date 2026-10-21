/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.Nilpotent

/-!
# Henselianity of infinitesimal local quotients

A quotient by a positive power of the maximal ideal is a nonzero local ring
with nilpotent maximal ideal. The Henselian structure is proved from these
facts, without a Noetherian hypothesis or a Henselian hypothesis on the base.
-/

@[expose] public section

open IsLocalRing

namespace HenselianLocalRing

/-- Positive infinitesimal quotients of any local ring are Henselian. -/
theorem quotient_maximalIdeal_pow (R : Type*) [CommRing R] [IsLocalRing R]
    (n : ℕ) (hn : n ≠ 0) : HenselianLocalRing (R ⧸ maximalIdeal R ^ n) := by
  let J := maximalIdeal R ^ n
  let : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top (Ideal.pow_le_self hn))
  let : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  apply of_maximalIdeal_pow_eq_bot (R ⧸ J) (n := n)
  rw [← IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective, ← Ideal.map_pow]
  exact Ideal.map_quotient_self J

end HenselianLocalRing
