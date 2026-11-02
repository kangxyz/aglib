/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # A principal open with nonempty original field fibres

The range of a nonempty open-map scheme morphism to an affine scheme contains
a nonempty basic open. The native pullback range formula then gives nonempty
fibres over every field map on which that same basic-open element is nonzero.
No surjectivity, Noetherian, domain, or section hypothesis is required.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- An original open map with nonempty source has nonempty original field
fibres over one nonzero principal base open. The element is nonzero because
its basic open contains the image of an actual source point. -/
theorem exists_ne_zero_nonempty_field_pullbacks_of_isOpenMap
    (R : Type u) [CommRing R] {X : Scheme.{u}} [Nonempty X]
    (f : X ⟶ Spec (.of R)) (hf : IsOpenMap f) :
    ∃ r : R, r ≠ 0 ∧ ∀ (L : Type u) [Field L] [Algebra R L],
      algebraMap R L r ≠ 0 → Nonempty (pullback f (Spec.algebraMap R L) : Scheme.{u}) := by
  classical
  let x : X := Classical.choice inferInstance
  have hopen : IsOpen (Set.range f) := by
    simpa only [Set.image_univ] using hf Set.univ isOpen_univ
  obtain ⟨_, ⟨r, rfl⟩, hxr, hrange⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hopen (f x) ⟨x, rfl⟩
  have hr : r ≠ 0 := by
    intro h
    apply (PrimeSpectrum.mem_basicOpen r (f x)).mp hxr
    rw [h]
    exact Ideal.zero_mem _
  refine ⟨r, hr, ?_⟩
  intro L _ _ hrL
  let z : Spec (.of L) := ⟨⊥, inferInstance⟩
  have hz : (Spec.algebraMap R L) z ∈ PrimeSpectrum.basicOpen r := by
    change algebraMap R L r ∉ (⊥ : Ideal L)
    simpa only [Ideal.mem_bot] using hrL
  have hzrange : z ∈ Set.range (pullback.snd f (Spec.algebraMap R L)) := by
    rw [Scheme.Pullback.range_snd]
    exact hrange hz
  obtain ⟨y, _⟩ := hzrange
  exact ⟨y⟩

end AlgebraicGeometry.Scheme
