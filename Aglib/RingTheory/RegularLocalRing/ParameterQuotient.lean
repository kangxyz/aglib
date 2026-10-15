/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.LocalRing.ParameterQuotient
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Quotients by first regular-local parameters

Killing an element of the maximal ideal outside its square preserves regular locality and lowers
dimension by one. Domain and scalar regularity are conclusions of later results, not extra
premises here.

## Extraction basis

Transferred subsets of `Quillen.Algebra.RegularLocal.ParameterQuotient` at revision
`83629578a3d70787d41ec631f5234af8758716af`, source SHA-256
`848871057c33da3a84886d133b551c6c063b184f723f36db1409937abb1bfd8a`. Objects, universes,
canonical maps and
actual premises are retained; declarations use native mathematical namespaces.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open IsLocalRing Module

namespace IsRegularLocalRing
variable (R : Type u) [CommRing R]
/-- Quotienting a regular local ring by an element outside the square of its
maximal ideal gives a regular local ring of dimension one less. Neither a
domain instance nor scalar regularity is assumed in this theorem. -/
theorem regularLocal_quotient_parameter [IsRegularLocalRing R]
    (d : ℕ) (hd : ringKrullDim R = (d + 1 : ℕ))
    (x : R) (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧
      ringKrullDim (R ⧸ Ideal.span {x}) = (d : ℕ) := by
  have hne : Ideal.span {x} ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
      ((Ideal.span_singleton_le_iff_mem (maximalIdeal R)).mpr hx)
  have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (R ⧸ Ideal.span {x}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  have hc : Module.finrank (ResidueField R) (CotangentSpace R) = d + 1 := by
    have he := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
    rw [hd] at he
    exact_mod_cast he
  have hgen := IsLocalRing.spanFinrank_maximalIdeal_quotient_parameter_le R d hc.le x hx hx2
  have hupper : ringKrullDim (R ⧸ Ideal.span {x}) ≤ (d : ℕ) :=
    (ringKrullDim_le_spanFinrank_maximalIdeal _).trans (by exact_mod_cast hgen)
  have hlow' : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by
    rw [← hd, ← maximalIdeal_height_eq_ringKrullDim]
    exact Ideal.height_le_ringKrullDim_quotient_add_one hx
  have hlower : (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ Ideal.span {x}) := by
    apply (ENat.WithBot.add_le_add_natCast_right_iff (c := 1)).mp
    simpa only [Nat.cast_add, Nat.cast_one] using hlow'
  have heq := le_antisymm hupper hlower
  refine ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_, heq⟩
  rw [heq]
  exact_mod_cast hgen

end IsRegularLocalRing
