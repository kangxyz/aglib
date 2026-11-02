/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.FrobeniusKernel.Module
public import Aglib.RingTheory.Unramified.GenericFinite

/-!
# Generic finite etale scalar extension of the original kernel equations

The literal tensor algebra still represents fixed points of the original map,
with the exact unit-tensor coordinate formula and naturality. Over a Noetherian
domain the actual etale quotient becomes finite after a nonzero shrinking.
This is algebraic representability; no scheme/sheaf comparison is asserted.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Module

namespace Algebra.FrobeniusKernel

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
  {ι : Type*} [Fintype ι] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
  (Φ : M →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hA] M) (b : Basis ι A M)
  (R : Type*) [CommRing R] [Algebra A R]
  (S : Type*) [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower A R S]

/-- Base change of the actual equation algebra represents the original fixed
points over the new scalar algebra. -/
def homBaseChangeEquivFixed :
    (R ⊗[A] CoordinateAlgebra p (coefficientMatrix p hp hA Φ b) →ₐ[R] S) ≃
      {z : S ⊗[A] M // LinearMap.frobeniusBaseChange p hp hA Φ S z = z} :=
  (AlgHom.liftEquiv A R (CoordinateAlgebra p (coefficientMatrix p hp hA Φ b)) S).symm.trans
    (homEquivFixed p hp hA Φ b S)

/-- Forward evaluation retains the original coordinate and the unit tensor. -/
theorem homBaseChangeEquivFixed_repr
    (h : R ⊗[A] CoordinateAlgebra p (coefficientMatrix p hp hA Φ b) →ₐ[R] S) (i : ι) :
    (b.baseChange S).repr (homBaseChangeEquivFixed p hp hA Φ b R S h).val i =
      h (1 ⊗ₜ[A] coordinate p (coefficientMatrix p hp hA Φ b) i) := by
  exact homEquivFixed_repr p hp hA Φ b S _ i

variable {S} {T : Type*} [CommRing T] [Algebra A T] [Algebra R T] [IsScalarTower A R T]

/-- Naturality uses the original tensor map, not a coordinate-defined substitute. -/
theorem homBaseChangeEquivFixed_naturality (f : S →ₐ[R] T)
    (h : R ⊗[A] CoordinateAlgebra p (coefficientMatrix p hp hA Φ b) →ₐ[R] S) :
    (homBaseChangeEquivFixed p hp hA Φ b R T (f.comp h)).val =
      _root_.TensorProduct.map (f.restrictScalars A).toLinearMap LinearMap.id
        (homBaseChangeEquivFixed p hp hA Φ b R S h).val := by
  let g : CoordinateAlgebra p (coefficientMatrix p hp hA Φ b) →ₐ[A] S :=
    (AlgHom.liftEquiv A R (CoordinateAlgebra p (coefficientMatrix p hp hA Φ b)) S).symm h
  have hg :
      (AlgHom.liftEquiv A R (CoordinateAlgebra p (coefficientMatrix p hp hA Φ b)) T).symm
        (f.comp h) = (f.restrictScalars A).comp g := by
    apply AlgHom.ext
    intro x
    rfl
  simp only [homBaseChangeEquivFixed, Equiv.trans_apply]
  rw [hg]
  exact homEquivFixed_naturality p hp hA Φ b (f.restrictScalars A) g

/-- The actual coordinate algebra is finite etale after a nonzero shrinking.
The preceding comparison supplies its original-map interpretation on every
new test algebra; no matrix invertibility is required. -/
theorem exists_ne_zero_finite_etale_baseChange [IsDomain A] [IsNoetherianRing A] :
    ∃ a : A, a ≠ 0 ∧
      Module.Finite (Localization.Away a)
        ((Localization.Away a) ⊗[A] CoordinateAlgebra p (coefficientMatrix p hp hA Φ b)) ∧
      Algebra.Etale (Localization.Away a)
        ((Localization.Away a) ⊗[A] CoordinateAlgebra p (coefficientMatrix p hp hA Φ b)) := by
  let : Algebra.Etale A (CoordinateAlgebra p (coefficientMatrix p hp hA Φ b)) :=
    etale p _ hA
  obtain ⟨a, ha, hfinite⟩ := Algebra.FormallyUnramified.exists_ne_zero_finite_baseChange
    (A := A) (C := CoordinateAlgebra p (coefficientMatrix p hp hA Φ b))
  exact ⟨a, ha, hfinite, inferInstance⟩

end Algebra.FrobeniusKernel
