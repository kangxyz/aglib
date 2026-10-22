/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.ReesAlgebra.Grading
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-!
# The coefficientwise map of actual Rees algebras

The original polynomial map restricts to the native Rees algebras of `I`
and `I.map f`. A surjective coefficient map gives surjectivity in every
homogeneous degree, retaining the actual ideal powers and polynomial grading.
-/

@[expose] public noncomputable section

open Polynomial Graded

universe u v

namespace reesAlgebra

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- The actual polynomial coefficient map, restricted to the original Rees algebras. -/
def map (f : A →+* B) (I : Ideal A) : grading I →+*ᵍ grading (I.map f) where
  toFun p := ⟨(p : A[X]).map f, by
    intro n
    rw [Polynomial.coeff_map, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem f (p.property n)⟩
  map_one' := by apply Subtype.ext; exact Polynomial.map_one f
  map_mul' p q := by apply Subtype.ext; exact Polynomial.map_mul f
  map_zero' := by apply Subtype.ext; exact Polynomial.map_zero f
  map_add' p q := by apply Subtype.ext; exact Polynomial.map_add f
  map_mem {n} {p} hp := by
    intro m hm
    change ((p : A[X]).map f).coeff m = 0
    rw [coeff_map, hp m hm, map_zero]

@[simp]
theorem map_coe (f : A →+* B) (I : Ideal A) (p : reesAlgebra I) :
    (map f I p : B[X]) = (p : A[X]).map f := rfl

/-- Every coefficient in the image ideal power has an original coefficient lift. -/
theorem map_degreewise_surjective (f : A →+* B) (hf : Function.Surjective f)
    (I : Ideal A) (n : ℕ) : Function.Surjective ((map f I).gradedAddHom n) := by
  intro p
  have hp : ((p : reesAlgebra (I.map f)) : B[X]).coeff n ∈ (I ^ n).map f := by
    rw [Ideal.map_pow]
    exact (p : reesAlgebra (I.map f)).property n
  obtain ⟨a, ha, he⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hp
  refine ⟨homogeneous I n ⟨a, ha⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change (monomial n a).map f = ((p : reesAlgebra (I.map f)) : B[X])
  rw [Polynomial.map_monomial, he]
  exact (eq_monomial_coeff p.property).symm

/-- The original irrelevant ideal has enough images to define the native Proj map. -/
theorem irrelevant_le_map (f : A →+* B) (hf : Function.Surjective f) (I : Ideal A) :
    HomogeneousIdeal.irrelevant (grading (I.map f)) ≤
      (HomogeneousIdeal.irrelevant (grading I)).map (map f I) := by
  apply toIdeal_le_toIdeal_iff.mp
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  obtain ⟨a, ha⟩ := map_degreewise_surjective f hf I n ⟨p, hp⟩
  have he : map f I (a : reesAlgebra I) = p := congrArg Subtype.val ha
  rw [← he]
  exact Ideal.mem_map_of_mem _
    (HomogeneousIdeal.mem_irrelevant_of_mem _ hn a.property)

end reesAlgebra
