/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Primitive roots at an actual filtered stage

A specified primitive root in a filtered colimit descends after any given
stage. Only its power equation needs equality descent; primitivity follows
from its exact image, without injective transition maps or domain hypotheses.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace CommRingCat

universe u

/-- Descend a specified primitive root, retaining its exact image and an
actual transition from any prescribed stage. -/
theorem exists_primitiveRoot_rep_over
    {I : Type u} [Category.{u} I] [IsFiltered I]
    (D : I ⥤ CommRingCat.{u}) (c : Cocone D) (hc : IsColimit c)
    {n : ℕ} {ζ : c.pt} (hζ : IsPrimitiveRoot ζ n) (i : I) :
    ∃ (j : I) (_ : i ⟶ j) (a : D.obj j),
      c.ι.app j a = ζ ∧ IsPrimitiveRoot a n := by
  obtain ⟨j, f, a, ha⟩ := Concrete.exists_hom_ι_eq_of_isColimit D hc ζ i
  have heq : c.ι.app j (a ^ n) = c.ι.app j 1 := by
    rw [map_pow, ha, hζ.pow_eq_one, map_one]
  obtain ⟨k, g, hg⟩ := hc.eq_iff' (a ^ n) 1 |>.mp heq
  refine ⟨k, f ≫ g, D.map g a, ?_, ?_⟩
  · calc
      c.ι.app k (D.map g a) = c.ι.app j a :=
        ConcreteCategory.congr_hom (c.w g) a
      _ = ζ := ha
  · constructor
    · simpa only [map_pow, map_one] using hg
    · intro m hm
      apply hζ.dvd_of_pow_eq_one m
      have himage : c.ι.app k (D.map g a) = ζ :=
        (ConcreteCategory.congr_hom (c.w g) a).trans ha
      rw [← himage, ← map_pow, hm, map_one]

end CommRingCat
