/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Blowup.DoubleLine.Marked.Chart
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Actual initial double-line coordinates

A nonzero linear-square full canonical kernel is normalized on actual original
maximal-ideal generators. Only residue lifts are chosen; the existing original
polynomial shears, permutation laws and cone presentation are reused.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open scoped BigOperators

universe u

namespace MvPolynomial

variable {k : Type u} [Field k]

/-- A nonzero original linear form is monic in one permuted coordinate up to
an original nonzero scalar; no square root or field extension is chosen. -/
private theorem exists_monic_middle_linear_form {L : MvPolynomial (Fin 3) k}
    (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0) :
    ∃ (i : Fin 3) (a b d : k), d ≠ 0 ∧
      renameEquiv k (Equiv.swap i 1) L =
        C d * (X 1 + C a * X 0 + C b * X 2) := by
  classical
  have hmem : L ∈ Submodule.span k (Set.range (X : Fin 3 → MvPolynomial (Fin 3) k)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact hL
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hmem
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    apply hL0
    rw [← hc]
    simp only [h, zero_smul, Finset.sum_const_zero]
  let e : Fin 3 ≃ Fin 3 := Equiv.swap i 1
  have hsum : renameEquiv k e L = ∑ j, c (e j) • (X j : MvPolynomial (Fin 3) k) := by
    rw [← hc, map_sum]
    simp only [map_smul, renameEquiv_apply, rename_X]
    apply Fintype.sum_equiv e
    intro j
    simp only [e, Equiv.swap_apply_self]
  have hm : c (e 1) = c i := by simp [e]
  refine ⟨i, (c i)⁻¹ * c (e 0), (c i)⁻¹ * c (e 2), c i, hi, ?_⟩
  change renameEquiv k e L = _
  rw [hsum, Fin.sum_univ_three]
  simp only [Algebra.smul_def, algebraMap_eq, hm, map_mul]
  have hcancel : C (c i) * C ((c i)⁻¹) = (1 : MvPolynomial (Fin 3) k) := by
    rw [← map_mul, mul_inv_cancel₀ hi, map_one]
  linear_combination -(C (c (e 0)) * X 0 + C (c (e 2)) * X 2) * hcancel

end MvPolynomial

namespace IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The existing two-coefficient shear, conjugated by the original permutation,
normalizes the full monic linear-square kernel on actual ideal elements. -/
private theorem cotangentKernel_middleShift (g : Fin 3 → maximalIdeal A) (α γ : A)
    (hker : doubleLineChildCotangentKernel A g = Ideal.span
      {(MvPolynomial.X 1 + MvPolynomial.C (residue A α) * MvPolynomial.X 0 +
        MvPolynomial.C (residue A γ) * MvPolynomial.X 2) ^ 2}) :
    doubleLineChildCotangentKernel A
        ![g 0, g 1 + α • g 0 + γ • g 2, g 2] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2} := by
  let τ : Fin 3 ≃ Fin 3 := Equiv.swap 0 1
  let ρ := MvPolynomial.renameEquiv (ResidueField A) τ
  let σ := (ρ.trans (MvPolynomial.otherShift (residue A α) (residue A γ))).trans ρ
  let g₁ := g ∘ τ
  let g₂ := otherShiftTriple g₁ α γ
  let g₃ := g₂ ∘ τ
  have hg : g₃ = ![g 0, g 1 + α • g 0 + γ • g 2, g 2] := by
    funext i
    fin_cases i <;> simp [g₃, g₂, g₁, τ, otherShiftTriple, Equiv.swap_apply_def]
  have hmap : (Ideal.cotangentPolynomialMap (maximalIdeal A) g₃).toRingHom =
      (Ideal.cotangentPolynomialMap (maximalIdeal A) g).toRingHom.comp σ.toRingHom := by
    apply RingHom.ext
    intro p
    change Ideal.cotangentPolynomialMap (maximalIdeal A) g₃ p =
      Ideal.cotangentPolynomialMap (maximalIdeal A) g (σ p)
    rw [show g₃ = (fun i => g₂ (τ i)) from rfl, cotangentPolynomialMap_permutation]
    rw [show g₂ = otherShiftTriple g₁ α γ from rfl, cotangentPolynomialMap_otherShift]
    rw [show g₁ = (fun i => g (τ i)) from rfl, cotangentPolynomialMap_permutation]
    rfl
  have hσ : σ (MvPolynomial.X 1) =
      MvPolynomial.X 1 + MvPolynomial.C (residue A α) * MvPolynomial.X 0 +
        MvPolynomial.C (residue A γ) * MvPolynomial.X 2 := by
    simp [σ, ρ, τ, MvPolynomial.otherShift, MvPolynomial.otherShiftHom,
      MvPolynomial.renameEquiv_apply, Equiv.swap_apply_def]
  have hspan : (Ideal.span {(MvPolynomial.X 1 :
      MvPolynomial (Fin 3) (ResidueField A)) ^ 2}).map σ.toRingHom =
      Ideal.span {(MvPolynomial.X 1 + MvPolynomial.C (residue A α) * MvPolynomial.X 0 +
        MvPolynomial.C (residue A γ) * MvPolynomial.X 2) ^ 2} := by
    rw [Ideal.map_span, Set.image_singleton, map_pow]
    change Ideal.span {(σ (MvPolynomial.X 1)) ^ 2} = _
    rw [hσ]
  have hcomp : doubleLineChildCotangentKernel A g₃ =
      (doubleLineChildCotangentKernel A g).comap σ.toRingHom := by
    ext p
    change (Ideal.cotangentPolynomialMap (maximalIdeal A) g₃).toRingHom p = 0 ↔
      (Ideal.cotangentPolynomialMap (maximalIdeal A) g).toRingHom (σ p) = 0
    rw [hmap]
    rfl
  rw [← hg, hcomp, hker, ← hspan]
  exact Ideal.comap_map_of_bijective σ.toRingHom σ.bijective

end IsLocalRing

namespace Ideal

variable {A : Type u} [CommRing A]

/-- The same original generating ideal after the middle-coordinate shear. -/
private theorem span_triple_middleShift (t s z α γ : A) :
    span ({t, s, z + α * s + γ * t} : Set A) = span ({t, s, z} : Set A) := by
  rw [Set.insert_comm t s, span_insert, span_pair_add_mul_left, ← span_insert,
    Set.insert_comm s t, span_insert, span_pair_add_mul_left, ← span_insert]

end Ideal

namespace IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The initial double-line kernel can be normalized on actual generators
of the same original maximal ideal, using only residue lifts. -/
theorem exists_original_doubleLine_generators
    (g : Fin 3 → maximalIdeal A)
    (hgen : Ideal.span (Set.range fun i => (g i : A)) = maximalIdeal A)
    (L : MvPolynomial (Fin 3) (ResidueField A)) (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0)
    (hker : doubleLineChildCotangentKernel A g = Ideal.span {L ^ 2}) :
    ∃ t s z : maximalIdeal A,
      maximalIdeal A = Ideal.span ({(t : A), (s : A), (z : A)} : Set A) ∧
        doubleLineChildCotangentKernel A ![s, z, t] =
          Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2} := by
  classical
  obtain ⟨i, a, b, d, hd, he⟩ := MvPolynomial.exists_monic_middle_linear_form hL hL0
  obtain ⟨α, hα⟩ := residue_surjective (R := A) a
  obtain ⟨γ, hγ⟩ := residue_surjective (R := A) b
  let e : Fin 3 ≃ Fin 3 := Equiv.swap i 1
  let σ := MvPolynomial.renameEquiv (ResidueField A) e
  let g' : Fin 3 → maximalIdeal A := fun j => g (e j)
  have hσ : ∀ p, σ (σ p) = p := by
    intro p
    change MvPolynomial.rename e (MvPolynomial.rename e p) = p
    rw [MvPolynomial.rename_rename]
    have hcomp : (e : Fin 3 → Fin 3) ∘ e = id := by
      funext j
      exact Equiv.swap_apply_self i 1 j
    rw [hcomp, MvPolynomial.rename_id_apply]
  have hcomp : doubleLineChildCotangentKernel A g' =
      (doubleLineChildCotangentKernel A g).comap σ.toRingHom := by
    ext p
    change Ideal.cotangentPolynomialMap (maximalIdeal A) g' p = 0 ↔
      Ideal.cotangentPolynomialMap (maximalIdeal A) g (σ p) = 0
    rw [show g' = (fun j => g (e j)) from rfl, cotangentPolynomialMap_permutation]
    rfl
  have hspan : (Ideal.span {(σ L) ^ 2}).map σ.toRingHom = Ideal.span {L ^ 2} := by
    rw [Ideal.map_span, Set.image_singleton, map_pow]
    change Ideal.span {(σ (σ L)) ^ 2} = Ideal.span {L ^ 2}
    rw [hσ]
  have hk : doubleLineChildCotangentKernel A g' = Ideal.span {(σ L) ^ 2} := by
    rw [hcomp, hker, ← hspan]
    exact Ideal.comap_map_of_bijective σ.toRingHom σ.bijective
  have hm : doubleLineChildCotangentKernel A g' =
      Ideal.span {(MvPolynomial.X 1 + MvPolynomial.C a * MvPolynomial.X 0 +
        MvPolynomial.C b * MvPolynomial.X 2) ^ 2} := by
    rw [hk, show σ L = _ from he, mul_pow, ← map_pow]
    exact Ideal.span_singleton_mul_left_unit
      ((isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hd)).map
        (MvPolynomial.C : ResidueField A →+* MvPolynomial (Fin 3) (ResidueField A))) _
  have hn := cotangentKernel_middleShift g' α γ (by simpa only [hα, hγ] using hm)
  refine ⟨g' 2, g' 0, g' 1 + α • g' 0 + γ • g' 2, ?_, hn⟩
  have hrange : Set.range (fun j => (g' j : A)) = Set.range (fun j => (g j : A)) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨e.symm j, by simp [g']⟩
  have hset : Set.range (fun j => (g' j : A)) =
      ({(g' 2 : A), (g' 0 : A), (g' 1 : A)} : Set A) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp
    · intro hx
      rcases hx with h | h | h
      · exact ⟨2, h.symm⟩
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
  have hgen' : maximalIdeal A = Ideal.span ({(g' 2 : A), (g' 0 : A), (g' 1 : A)} : Set A) := by
    rw [← hset, hrange, hgen]
  change maximalIdeal A =
    Ideal.span ({(g' 2 : A), (g' 0 : A), (g' 1 : A) + α * (g' 0 : A) + γ * (g' 2 : A)} : Set A)
  rw [Ideal.span_triple_middleShift]
  exact hgen'


end IsLocalRing
