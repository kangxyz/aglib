/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.FrobeniusEquation.Module
public import Aglib.LinearAlgebra.FrobeniusBaseChange.Tower

/-!
# Inhomogeneous roots after an original scalar extension becomes free

The free intermediate tensor module is only used inside the construction.
Native cancellation returns the root to the original tensor module, and the
original Frobenius and tensor-map squares preserve its inhomogeneous equation.
The actual root algebra and its compatible structural maps are retained.
-/

@[expose] public noncomputable section

universe u v w t

open scoped TensorProduct

namespace Algebra.FrobeniusEquation

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
  [Module.Finite A M]
  (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
  (Φ : M →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hA] M)
  (R : Type t) [CommRing R] [Algebra A R] [Module.Free R (R ⊗[A] M)]
  (S : Type w) [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower A R S]

/-- Freeness after scalar extension suffices for actual roots of every original
inhomogeneous tensor equation on a spectrum-surjective etale extension. -/
theorem exists_etale_surjective_solution_of_free_baseChange (y : S ⊗[A] M) :
    ∃ (C : Type w) (_ : CommRing C) (_ : Algebra S C) (_ : Algebra R C)
      (_ : Algebra A C) (_ : IsScalarTower R S C) (_ : IsScalarTower A R C)
      (_ : IsScalarTower A S C),
      Algebra.Etale S C ∧
      Function.Surjective (PrimeSpectrum.comap (algebraMap S C)) ∧
      ∃ z : C ⊗[A] M, LinearMap.frobeniusBaseChange p hp hA Φ C z - z =
        _root_.TensorProduct.map (IsScalarTower.toAlgHom A S C).toLinearMap LinearMap.id y := by
  let eS := TensorProduct.AlgebraTensorModule.cancelBaseChange A R S S M
  obtain ⟨C, hC, hSC, hRC, hRSC, hetale, hsurj, z, hz⟩ :=
    exists_etale_surjective_solution p hp (LinearMap.primeCast_eq_zero_baseChange p hA R)
      (LinearMap.frobeniusBaseChange p hp hA Φ R) S (eS.symm y)
  let : Algebra A C := Algebra.compHom C (algebraMap A R)
  let : IsScalarTower A R C :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := R) (A := C) fun _ => rfl
  let : IsScalarTower A S C :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := S) (A := C) fun a => by
      change algebraMap R C (algebraMap A R a) = algebraMap S C (algebraMap A S a)
      rw [IsScalarTower.algebraMap_apply A R S, IsScalarTower.algebraMap_apply R S C]
  let eC := TensorProduct.AlgebraTensorModule.cancelBaseChange A R C C M
  have hf : (IsScalarTower.toAlgHom R S C).restrictScalars A =
      IsScalarTower.toAlgHom A S C := by
    ext x
    rfl
  refine ⟨C, hC, hSC, hRC, inferInstance, hRSC, inferInstance, inferInstance,
    hetale, hsurj, eC z, ?_⟩
  have h := congrArg eC hz
  dsimp only [eC, eS] at h
  simp only [map_sub, LinearMap.frobeniusBaseChange_cancelBaseChange,
    LinearMap.cancelBaseChange_tensor_map, LinearEquiv.apply_symm_apply] at h
  rw [hf] at h
  exact h

end Algebra.FrobeniusEquation
