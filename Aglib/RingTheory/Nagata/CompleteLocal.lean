/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.CompleteLocal
public import Aglib.RingTheory.Nagata.Normalization
public import Aglib.RingTheory.Nagata.ReducedCompletion

/-!
# Complete Noetherian local rings are Nagata

The arbitrary-domain finite-normalization theorem applies to every literal
prime quotient with its original quotient map and maximal-adic completeness.
The resulting Nagata property gives finite normalization of the original
reduced ring in its supplied total quotient ring. No dimension restriction
or normality assumption is imposed on the complete local base.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

/-- Every complete Noetherian local ring of any finite dimension bound is Nagata,
using its actual prime quotients and auxiliary extension-field universe zero. -/
theorem IsNagataRing.of_complete_local_dimLE
    (d : ℕ) (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] (hd : ringKrullDim A ≤ (d : ℕ)) :
    IsNagataRing.{u, 0} A := by
  refine ⟨inferInstance, ?_⟩
  intro p hp
  let : IsNoetherianRing (A ⧸ p) := isNoetherianRing_of_surjective A (A ⧸ p)
    (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  let : IsLocalRing (A ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  let : IsAdicComplete (maximalIdeal (A ⧸ p)) (A ⧸ p) := by
    have h := IsAdicComplete.map_algebraMap_of_finite A (maximalIdeal A) (A ⧸ p)
    rwa [IsLocalRing.map_maximalIdeal_of_surjective
      (algebraMap A (A ⧸ p)) Ideal.Quotient.mk_surjective] at h
  exact IsJapaneseRing.of_complete_local_dimLE d (A ⧸ p) ((ringKrullDim_quotient_le p).trans hd)

/-- Every complete Noetherian local ring is Nagata in auxiliary test universe zero. -/
theorem IsNagataRing.of_complete_local
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] : IsNagataRing.{u, 0} A := by
  apply IsNagataRing.of_complete_local_dimLE (maximalIdeal A).spanFinrank A
  rw [← maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast (maximalIdeal A).height_le_spanFinrank (maximalIdeal.isMaximal A).ne_top

/-- A local domain finite over a complete Noetherian local ring has reduced
maximal-adic completion, with no dimension restriction. -/
theorem AdicCompletion.isReduced_of_finite_over_complete_local
    (A B : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra A B] [Module.Finite A B] :
    IsReduced (AdicCompletion (maximalIdeal B) B) :=
  ((IsNagataRing.of_complete_local A).of_finite (S := B)).isReduced_completion

/-- The literal normalization of a complete reduced Noetherian local ring in
its original total quotient ring is finite, in every supplied quotient-ring universe. -/
theorem integralClosure.finite_of_complete_local_reduced
    (R : Type u) [CommRing R] [IsReduced R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (Q : Type v) [CommRing Q] [Algebra R Q] [IsFractionRing R Q] :
    Module.Finite R (integralClosure R Q) :=
  integralClosure.finite_of_isNagataRing R (IsNagataRing.of_complete_local R) Q
