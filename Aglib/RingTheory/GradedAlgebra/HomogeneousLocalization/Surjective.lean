/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Surjectivity on actual homogeneous localization charts

A degreewise-surjective graded ring map induces a surjection on every native
homogeneous localization away from a homogeneous element. No regularity of
the element, or reducedness of either ring, is required.
-/

@[expose] public section

open Graded

namespace HomogeneousLocalization

variable {ι A B σ τ : Type*} [AddCommMonoid ι] [DecidableEq ι]
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- Lift the homogeneous numerator, retaining the original denominator power. -/
theorem Away.map_surjective_of_degreewise_surjective (f : 𝒜 →+*ᵍ ℬ)
    (hf : ∀ n, Function.Surjective (f.gradedAddHom n))
    {d : ι} {s : A} (hs : s ∈ 𝒜 d) :
    Function.Surjective (Away.map f s) := by
  intro z
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (map_mem f hs) z
  obtain ⟨a, ha⟩ := hf (n • d) ⟨b, hb⟩
  have hab : f (a : A) = b := congrArg Subtype.val ha
  refine ⟨Away.mk 𝒜 hs n a a.property, ?_⟩
  simp only [Away.map_mk, hab]

end HomogeneousLocalization
