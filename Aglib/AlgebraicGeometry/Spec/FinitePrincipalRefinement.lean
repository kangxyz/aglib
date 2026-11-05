/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PrincipalBaseChangeLimit

/-! # One actual principal stage refining a finite family

Multiply the original stage denominators in the original denominator monoid.
The singleton stage of this product lies in every original stage open. Its
inverse images give actual open-scheme inclusions over each original family.
For a domain and nonzero denominators the common base open is nonempty. No
claim is made that it contains any prescribed closed point.
-/

@[expose] public noncomputable section

open CategoryTheory
open IsLocalization.PrincipalDiagram
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit

universe u v

variable {R : Type u} [CommRing R] (M : Submonoid R)

/-- The original principal stage has exactly the original denominator's
basic-open image. -/
theorem stageBaseOpen_eq_basicOpen (s : Finset M) :
    stageBaseOpen M s = PrimeSpectrum.basicOpen (denominator M s) := by
  exact Scheme.Hom.opensRange_localizationAway
    (R := CommRingCat.of R) (denominator M s)

/-- Divisibility of the original denominators gives the actual open inclusion. -/
theorem stageBaseOpen_le_of_dvd {s t : Finset M}
    (h : denominator M s ∣ denominator M t) :
    stageBaseOpen M t ≤ stageBaseOpen M s := by
  rw [stageBaseOpen_eq_basicOpen, stageBaseOpen_eq_basicOpen]
  obtain ⟨r, hr⟩ := h
  rw [hr]
  exact PrimeSpectrum.basicOpen_mul_le_left _ _

/-- A singleton stage whose denominator is the product of all the given
original denominators. Repeated factors are retained in the product. -/
def finiteProductStage {ι : Type v} [Fintype ι] (s : ι → Finset M) : Finset M :=
  {⟨∏ i, denominator M (s i), M.prod_mem fun i _ => denominator_mem M (s i)⟩}

@[simp]
theorem denominator_finiteProductStage {ι : Type v} [Fintype ι]
    (s : ι → Finset M) :
    denominator M (finiteProductStage M s) = ∏ i, denominator M (s i) := by
  classical
  simp [finiteProductStage, denominator]

/-- The actual common base stage is contained in every supplied base stage. -/
theorem finiteProductStage_base_le {ι : Type v} [Fintype ι]
    (s : ι → Finset M) (i : ι) :
    stageBaseOpen M (finiteProductStage M s) ≤ stageBaseOpen M (s i) := by
  apply stageBaseOpen_le_of_dvd
  rw [denominator_finiteProductStage]
  exact Finset.dvd_prod_of_mem (fun j => denominator M (s j)) (Finset.mem_univ i)

/-- The common principal coefficient stage refines the actual inverse-image
open of every original family, with no change to its structural morphism. -/
theorem finiteProductStage_source_le {ι : Type v} [Fintype ι]
    (s : ι → Finset M) {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) (i : ι) :
    stageSourceOpen M p (finiteProductStage M s) ≤ stageSourceOpen M p (s i) :=
  p.preimage_mono (finiteProductStage_base_le M s i)

/-- The actual open-scheme refinement map into the supplied principal stage. -/
def finiteProductStageInclusion {ι : Type v} [Fintype ι]
    (s : ι → Finset M) {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) (i : ι) :
    (stageSourceOpen M p (finiteProductStage M s) : Scheme.{u}) ⟶
      (stageSourceOpen M p (s i) : Scheme.{u}) :=
  X.homOfLE (finiteProductStage_source_le M s p i)

@[reassoc (attr := simp)]
theorem finiteProductStageInclusion_over {ι : Type v} [Fintype ι]
    (s : ι → Finset M) {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) (i : ι) :
    finiteProductStageInclusion M s p i ≫ (stageSourceOpen M p (s i)).ι =
      (stageSourceOpen M p (finiteProductStage M s)).ι :=
  X.homOfLE_ι (finiteProductStage_source_le M s p i)

variable (R) [IsDomain R]

/-- Every actual principal stage of nonzero denominators contains the generic
point of the original domain. No fraction-field realization is needed. -/
theorem stageBaseOpen_nonempty_nonZeroDivisors (s : Finset R⁰) :
    Nonempty (stageBaseOpen R⁰ s) := by
  rw [stageBaseOpen_eq_basicOpen]
  refine ⟨⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩⟩
  change denominator R⁰ s ∉ (⊥ : Ideal R)
  simpa only [Ideal.mem_bot] using nonZeroDivisors.ne_zero (denominator_mem R⁰ s)

/-- The product stage has a genuinely nonzero denominator and a nonempty
base open, including for an empty indexing type. -/
theorem finiteProductStage_nonzero_nonempty {ι : Type v} [Fintype ι]
    (s : ι → Finset R⁰) :
    denominator R⁰ (finiteProductStage R⁰ s) ≠ 0 ∧
      Nonempty (stageBaseOpen R⁰ (finiteProductStage R⁰ s)) :=
  ⟨nonZeroDivisors.ne_zero (denominator_mem R⁰ _),
    stageBaseOpen_nonempty_nonZeroDivisors R _⟩

end AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit
