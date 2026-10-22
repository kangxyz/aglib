/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Propagating surjectivity through a generating square

A commuting square need not be a pushout for surjectivity to persist.
It is enough that the images of the old target and the new source jointly
generate the new target as a subring.
-/

@[expose] public section

open CategoryTheory

universe u

namespace CommRingCat

/-- Surjectivity propagates through a commuting square whose two incoming
images generate the new target. No pushout hypothesis is imposed. -/
lemma surjective_of_closure_range_union_range_eq_top
    {R S R' S' : CommRingCat.{u}}
    (f : R ⟶ S) (r : R ⟶ R') (s : S ⟶ S') (f' : R' ⟶ S')
    (hcomm : f ≫ s = r ≫ f')
    (hgenerate : Subring.closure (Set.range s ∪ Set.range f') = ⊤)
    (hsurj : Function.Surjective f) : Function.Surjective f' := by
  have hrange : Set.range s ⊆ f'.hom.range := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := hsurj x
    refine ⟨r z, ?_⟩
    exact (congr($(hcomm).hom z)).symm
  apply RingHom.range_eq_top.mp
  apply top_unique
  rw [← hgenerate]
  exact Subring.closure_le.mpr (Set.union_subset hrange (fun _ hx ↦ hx))

end CommRingCat
