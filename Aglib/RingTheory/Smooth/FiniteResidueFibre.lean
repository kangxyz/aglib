/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteType.FiniteResidue
public import Mathlib.RingTheory.Smooth.Flat

/-!
# Finite nonempty smooth residue fibres over integer algebras

Select a finite nonempty smooth residue fibre over finite-type integer algebra, preserving the
actual maximal ideal and fibreEvaluation map.

Source: `R5Lab.Aglib.AlgebraicGeometry.Morphisms.Smooth.FiniteFibre`, frozen R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`eb7b652fcb75babe827f8c2682f459183abea1b7b9498843d53dd59edaf11add`. Selected lines: [[22, 102]].
The actual objects, canonical maps, universes and stated premises are retained.
-/

@[expose] public section

open TensorProduct
open Algebra.FiniteType

noncomputable section

open TensorProduct

namespace Algebra.Smooth

universe u

/-- The same elementary integer Jacobson argument as the accepted
`FiniteResidue.lean` prerequisite, whose theorem is private there. -/
theorem integers_jacobson : IsJacobsonRing ℤ := by
  apply isJacobsonRing_iff_prime_eq.mpr
  intro P hP
  by_cases hP0 : P = ⊥
  · subst P
    apply le_antisymm _ Ideal.le_jacobson
    intro x hx
    have hu : IsUnit (x * x + 1) := (Ideal.mem_jacobson_bot.mp hx) x
    have hunit := Int.isUnit_iff.mp hu
    simp only [Ideal.mem_bot]
    rcases hunit with h | h <;> nlinarith [sq_nonneg x]
  · let : P.IsMaximal := hP.isMaximal hP0
    exact Ideal.jacobson_eq_self_of_isMaximal

/-- A maximal chart residue contracts to a maximal ideal of the actual
finite-type integer base. No faithfully flat hypothesis is needed. -/
theorem maximal_under_of_finiteType_int
    (A C : Type u) [CommRing A] [CommRing C] [Algebra ℤ A] [Algebra A C]
    [Algebra.FiniteType ℤ A] [Algebra.FiniteType A C]
    (m : Ideal C) [m.IsMaximal] : (m.under A).IsMaximal := by
  let : IsJacobsonRing ℤ := integers_jacobson
  let : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℤ) (B := A)
  let := Ideal.Quotient.field m
  let : Module.Finite A (C ⧸ m) := finite_of_finite_type_of_isJacobsonRing A (C ⧸ m)
  have hbot : ((⊥ : Ideal (C ⧸ m)).under A).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) (⊥ : Ideal (C ⧸ m))
  have heq : (⊥ : Ideal (C ⧸ m)).under A = m.under A := by
    ext x
    simp [Ideal.under_def, Ideal.mem_comap, ← Ideal.Quotient.mk_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem]
  exact heq ▸ hbot

/-- Evaluation on the actual fibre above the contracted chart point.
Its value on `1 ⊗ c` is the chart quotient of `c`. -/
def fibreEvaluation
    (A C : Type u) [CommRing A] [CommRing C] [Algebra A C] (m : Ideal C) :
    ((A ⧸ m.under A) ⊗[A] C) →+* (C ⧸ m) := by
  let : IsScalarTower A (A ⧸ m.under A) (C ⧸ m) :=
    IsScalarTower.of_algebraMap_eq' (by ext x; rfl)
  exact (Algebra.TensorProduct.lift (Algebra.ofId (A ⧸ m.under A) (C ⧸ m))
    (Ideal.Quotient.mkₐ A m) (fun _ _ => Commute.all _ _)).toRingHom

@[simp] theorem fibreEvaluation_one_tmul
    (A C : Type u) [CommRing A] [CommRing C] [Algebra A C] (m : Ideal C) (c : C) :
    fibreEvaluation A C m (1 ⊗ₜ[A] c) = Ideal.Quotient.mk m c := by
  simp [fibreEvaluation, Algebra.TensorProduct.lift_tmul]

/-- An actual nonzero smooth model over a finite-type integer base has a
nonzero smooth fibre over a finite maximal base residue field, obtained by
contracting an actual finite maximal chart residue. Both residue fields and
the fibre evaluation are constructed, with its original chart map fixed. -/
theorem exists_finite_nonempty_smooth_fibre
    (A C : Type u) [CommRing A] [CommRing C] [Nontrivial C]
    [Algebra ℤ A] [Algebra A C] [Algebra.FiniteType ℤ A] [Algebra.Smooth A C] :
    ∃ (m : Ideal C) (hm : m.IsMaximal) (hp : (m.under A).IsMaximal),
      letI := hm
      letI := hp
      letI := Ideal.Quotient.field m
      letI := Ideal.Quotient.field (m.under A)
      Finite (C ⧸ m) ∧ Finite (A ⧸ m.under A) ∧
      Algebra.Smooth (A ⧸ m.under A) ((A ⧸ m.under A) ⊗[A] C) ∧
      Nontrivial ((A ⧸ m.under A) ⊗[A] C) ∧
      ∀ c : C, fibreEvaluation A C m (1 ⊗ₜ[A] c) = Ideal.Quotient.mk m c := by
  let : Algebra.FiniteType ℤ C := by
    have hft := RingHom.FiniteType.comp
      (RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType A C))
      (RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType ℤ A))
    have heq : (algebraMap A C).comp (algebraMap ℤ A) = algebraMap ℤ C :=
      Subsingleton.elim _ _
    exact RingHom.finiteType_algebraMap.mp (heq ▸ hft)
  obtain ⟨m, hm, hfinite⟩ := exists_finite_maximal_quotient_int C
  let : m.IsMaximal := hm
  have hp : (m.under A).IsMaximal := maximal_under_of_finiteType_int A C m
  let : (m.under A).IsMaximal := hp
  let := Ideal.Quotient.field m
  let := Ideal.Quotient.field (m.under A)
  have hn : Nontrivial ((A ⧸ m.under A) ⊗[A] C) :=
    (fibreEvaluation A C m).domain_nontrivial
  exact ⟨m, hm, hp, hfinite, finite_quotient_of_finiteType_int A (m.under A),
    inferInstance, hn, fibreEvaluation_one_tmul A C m⟩

end Algebra.Smooth
