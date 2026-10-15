/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Reducedness of smooth algebras over domains

An étale algebra over a domain embeds into its generic fibre by flatness.
The unramified fibre over a field is reduced. Standard étale polynomial
presentations and localization then prove reducedness for every smooth
algebra over a domain. No field or characteristic assumption is imposed
on the base domain.

## Extraction basis

Transferred from `R5Lab.RingTheory.RegularLocalRing.Smooth` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`bc58a719836727c2f58b5e288e7baff0572303f818aa7f969bd8030b6f822fee`.
This module contains the three general reducedness lemmas `etale_isReduced`,
`standardSmooth_isReduced` and `smooth_isReduced` (source lines 42–77); all other source
interfaces remain outside this extraction.
-/

@[expose] public section

noncomputable section
namespace Algebra.Smooth
open Algebra IsLocalRing
open scoped _root_.TensorProduct

/-- An étale algebra over any domain is reduced, without a field or characteristic restriction. -/
lemma _root_.Algebra.Etale.etale_isReduced (R A : Type*) [CommRing R] [IsDomain R] [CommRing A]
    [Algebra R A] [Algebra.Etale R A] : IsReduced A := by
  let K := FractionRing R
  have : IsReduced (K ⊗[R] A) :=
    Algebra.FormallyUnramified.isReduced_of_field K _
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A)
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K))

/-- A standard smooth algebra over any domain is reduced, by its étale polynomial presentation. -/
lemma _root_.Algebra.IsStandardSmooth.standardSmooth_isReduced
    (R A : Type*) [CommRing R] [IsDomain R] [CommRing A]
    [Algebra R A] [Algebra.IsStandardSmooth R A] : IsReduced A := by
  obtain ⟨n, f, hf, hfe⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial
    (f := algebraMap R A) (by simpa [RingHom.isStandardSmooth_algebraMap])
  let := f.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin n) R) A := hfe
  exact Algebra.Etale.etale_isReduced (MvPolynomial (Fin n) R) A

/-- A smooth algebra over any domain is reduced. Localizations supply the proof; reducedness
is a conclusion, not an input. -/
lemma smooth_isReduced (R A : Type*) [CommRing R] [IsDomain R] [CommRing A]
    [Algebra R A] [Algebra.Smooth R A] : IsReduced A := by
  constructor
  intro x hx
  apply eq_zero_of_localization
  intro q hq
  obtain ⟨f, hfn, hf⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R q
  have : IsReduced (Localization.Away f) := Algebra.IsStandardSmooth.standardSmooth_isReduced R _
  have hx0 := (hx.map (algebraMap A (Localization.Away f))).eq_zero
  obtain ⟨⟨_, n, rfl⟩, heq⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f) x).mp hx0
  exact (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) x).mpr
    ⟨⟨f ^ n, q.primeCompl.pow_mem hfn n⟩, heq⟩

end Algebra.Smooth
