/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-! # Finite etale algebras over reduced bases

A finitely presented flat module is a retract of a finite free module. Its
coordinates are detected by all prime residue fields over a reduced ring.
Applying this to a finite etale algebra proves reducedness without a
Noetherian or domain hypothesis on the base.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Module

variable (R M : Type*) [CommRing R] [IsReduced R] [AddCommGroup M] [Module R M]
    [FinitePresentation R M] [Flat R M]

/-- Prime residue-field fibres detect elements of finitely presented flat
modules over arbitrary reduced commutative rings. -/
theorem eq_zero_of_residueField_tmul_eq_zero (x : M)
    (hx : ∀ (p : Ideal R) [p.IsPrime],
      (1 : p.ResidueField) ⊗ₜ[R] x = 0) : x = 0 := by
  obtain ⟨n, e, r, her⟩ :=
    Flat.exists_factorization_of_finitePresentation (LinearMap.id : M →ₗ[R] M)
  have he : e x = 0 := by
    ext i
    let l : M →ₗ[R] R := (Finsupp.lapply i).comp e
    have hl : IsNilpotent (l x) := by
      rw [nilpotent_iff_mem_prime]
      intro p hp
      let := hp
      apply Ideal.algebraMap_residueField_eq_zero.mp
      have h := congrArg
        (fun z : p.ResidueField ⊗[R] M =>
          TensorProduct.rid R p.ResidueField ((l.lTensor p.ResidueField) z)) (hx p)
      simpa only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
        map_zero, Algebra.smul_def, mul_one] using h
    exact hl.eq_zero
  have h := LinearMap.congr_fun her x
  simpa only [LinearMap.id_apply, LinearMap.comp_apply, he, map_zero] using h

end Module

namespace Algebra.Etale

variable (R A : Type*) [CommRing R] [IsReduced R] [CommRing A]
    [Algebra R A] [Module.Finite R A] [Algebra.Etale R A]

include R

/-- A finite etale algebra over an arbitrary reduced commutative ring is
reduced. In particular, the base need not be Noetherian or a domain. -/
theorem finite_isReduced : IsReduced A := by
  have : Module.FinitePresentation R A :=
    Module.FinitePresentation.of_finite_of_finitePresentation R A
  rw [isReduced_iff]
  intro x hx
  apply Module.eq_zero_of_residueField_tmul_eq_zero R A x
  intro p hp
  have : IsReduced (p.ResidueField ⊗[R] A) :=
    Algebra.FormallyUnramified.isReduced_of_field p.ResidueField _
  exact (hx.map (Algebra.TensorProduct.includeRight : A →ₐ[R] p.ResidueField ⊗[R] A)).eq_zero

end Algebra.Etale
