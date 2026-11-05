/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.RationalAdjunction
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.Data.ENat.SuccOrder

/-! # Closed-support dimension drop after an actual integral transformation

Integral incomparability controls dimension on the transformed coefficient
base. A non-zero-divisor in the actual closed ideal then gives a strict drop
relative to the original base's finite dimension bound. This permits support
induction across finite transformations, rather than falsely treating a
finite transform as a closed subscheme of its source.

No Noetherianity, normality, injectivity of the integral map, catenarity or
support-induction conclusion is assumed. The zero-dimensional endpoint also
constructs triviality of the actual closed quotient.
-/

@[expose] public section

open scoped nonZeroDivisors


namespace RingHom.IsIntegral

variable {R S : Type*} [CommRing R] [CommRing S]
  {f : R →+* S} (hf : f.IsIntegral)

include hf

/-- Integral incomparability sends every strict prime chain to a strict
prime chain downstairs, using the original ring homomorphism. -/
theorem ringKrullDim_le : ringKrullDim S ≤ ringKrullDim R := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.IsIntegral R S := ⟨hf⟩
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f)
  intro P Q hPQ
  exact Ideal.IsIntegral.under_lt_under hPQ

/-- The actual closed quotient drops at least one dimension after the
integral transformation whenever its defining ideal contains a regular element. -/
theorem closedSupport_succ_le (I : Ideal S) {s : S}
    (hs : s ∈ S⁰) (hsI : s ∈ I) :
    ringKrullDim (S ⧸ I) + 1 ≤ ringKrullDim R :=
  (ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective hs (Ideal.Quotient.eq_zero_iff_mem.mpr hsI)).trans
      hf.ringKrullDim_le

/-- A finite numerical bound on the original base makes the closed support
strictly smaller, without a separate finite-dimensionality certificate upstairs. -/
theorem closedSupport_lt (I : Ideal S) {s : S}
    (hs : s ∈ S⁰) (hsI : s ∈ I) (d : ℕ) (hd : ringKrullDim R ≤ (d : ℕ)) :
    ringKrullDim (S ⧸ I) < (d : ℕ) :=
  ENat.WithBot.add_one_le_natCast_iff.mp ((hf.closedSupport_succ_le I hs hsI).trans hd)

/-- The successor step supplies the actual smaller natural-number bound
needed by support induction, even when the quotient is empty or reducible. -/
theorem closedSupport_le_predecessor (I : Ideal S) {s : S}
    (hs : s ∈ S⁰) (hsI : s ∈ I) (d : ℕ)
    (hd : ringKrullDim R ≤ (d + 1 : ℕ)) :
    ringKrullDim (S ⧸ I) ≤ (d : ℕ) := by
  apply ENat.WithBot.lt_add_one_iff.mp
  simpa only [Nat.cast_add, Nat.cast_one] using hf.closedSupport_lt I hs hsI (d + 1) hd

/-- At rank zero the actual closed complement is empty: its quotient ring
is trivial. This establishes the induction endpoint rather than assuming it. -/
theorem closedSupport_subsingleton_of_dim_zero (I : Ideal S) {s : S}
    (hs : s ∈ S⁰) (hsI : s ∈ I) (hd : ringKrullDim R ≤ 0) :
    Subsingleton (S ⧸ I) := by
  apply ringKrullDim_eq_bot_iff_subsingleton.mp
  exact (ENat.WithBot.add_one_le_zero_iff _).mp
    ((hf.closedSupport_succ_le I hs hsI).trans hd)

/-- The coefficient principal localization used after target shrinking
still has the original base's bound; its closed complement drops one rank. -/
theorem localized_closedSupport_le_predecessor
    (M : Submonoid S) (L : Type*) [CommRing L] [Algebra S L] [IsLocalization M L]
    (I : Ideal L) {s : L} (hs : s ∈ L⁰) (hsI : s ∈ I) (d : ℕ)
    (hd : ringKrullDim R ≤ (d + 1 : ℕ)) :
    ringKrullDim (L ⧸ I) ≤ (d : ℕ) := by
  have hdrop : ringKrullDim (L ⧸ I) + 1 ≤ ringKrullDim R :=
    (ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective hs (Ideal.Quotient.eq_zero_iff_mem.mpr hsI)).trans
        ((IsLocalization.ringKrullDim_le S L M).trans hf.ringKrullDim_le)
  have hlt := ENat.WithBot.add_one_le_natCast_iff.mp (hdrop.trans hd)
  apply ENat.WithBot.lt_add_one_iff.mp
  simpa only [Nat.cast_add, Nat.cast_one] using hlt

end RingHom.IsIntegral

namespace Algebra

variable (R S : Type*) [CommRing R] [CommRing S]
  [Algebra R S] [Module.Finite R S]

/-- Finite coefficient transformations have the same strict-support bound.
The denominator is the actual element inverted in the coefficient base. -/
theorem finite_closedSupport_le_predecessor (I : Ideal S) {s : S}
    (hs : s ∈ S⁰) (hsI : s ∈ I) (d : ℕ)
    (hd : ringKrullDim R ≤ (d + 1 : ℕ)) :
    ringKrullDim (S ⧸ I) ≤ (d : ℕ) :=
  RingHom.IsIntegral.closedSupport_le_predecessor
    (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral R S)) I hs hsI d hd

/-- On a finite domain model every nonzero actual principal denominator
produces a strictly smaller closed complement. -/
theorem finite_domain_principalComplement_le_predecessor [IsDomain S]
    (s : S) (hs : s ≠ 0) (d : ℕ)
    (hd : ringKrullDim R ≤ (d + 1 : ℕ)) :
    ringKrullDim (S ⧸ Ideal.span {s}) ≤ (d : ℕ) :=
  finite_closedSupport_le_predecessor R S (Ideal.span {s})
    (mem_nonZeroDivisors_iff_ne_zero.mpr hs)
    (Ideal.subset_span (Set.mem_singleton s)) d hd

/-- Thin specialization to the literal localized finite coefficient model
and its actual nonzero principal-open denominator. -/
theorem finite_localized_principalComplement_le_predecessor
    (M : Submonoid S) (L : Type*) [CommRing L] [IsDomain L]
    [Algebra S L] [IsLocalization M L] (s : L) (hs : s ≠ 0) (d : ℕ)
    (hd : ringKrullDim R ≤ (d + 1 : ℕ)) :
    ringKrullDim (L ⧸ Ideal.span {s}) ≤ (d : ℕ) :=
  RingHom.IsIntegral.localized_closedSupport_le_predecessor
    (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral R S)) M L (Ideal.span {s})
      (mem_nonZeroDivisors_iff_ne_zero.mpr hs)
      (Ideal.subset_span (Set.mem_singleton s)) d hd

end Algebra
