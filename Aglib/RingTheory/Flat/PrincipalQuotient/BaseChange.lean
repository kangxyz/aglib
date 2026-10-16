/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Flat.PrincipalQuotient.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Base change of regular principal quotients

## Extraction basis

Transferred from `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`
at frozen dirty R5Lab revision `79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.
Source line ranges: 181–237, 2375–2394, 2725–2750, 3061–3077.
The original rings, modules, canonical maps, universes and hypotheses are retained.
-/

@[expose] public section

noncomputable section
open TensorProduct LinearMap

namespace Algebra
variable {R : Type*} [CommRing R]
open Module.Flat
section FaithfulBaseChange
variable (T : Type*) {S : Type*} [CommRing T] [CommRing S] [Algebra R T] [Algebra R S]

/-- Tensoring multiplication by `a` is multiplication by its actual tensor image. -/
theorem lTensor_mulLeft (a : S) :
    (LinearMap.mulLeft R a).lTensor T =
      LinearMap.mulLeft R (1 ⊗ₜ[R] a : T ⊗[R] S) := by
  apply _root_.TensorProduct.ext'
  intro t s
  simp [LinearMap.mulLeft_apply]

/-- Regularity of an equation is detected after a faithfully flat scalar extension. -/
theorem regular_tensor_iff [Module.FaithfullyFlat R T] (a : S) :
    IsSMulRegular (T ⊗[R] S) ((1 : T) ⊗ₜ[R] a) ↔ IsSMulRegular S a := by
  change Function.Injective (LinearMap.mulLeft R (1 ⊗ₜ[R] a : T ⊗[R] S)) ↔
    Function.Injective (LinearMap.mulLeft R a)
  rw [← lTensor_mulLeft T a]
  exact Module.FaithfullyFlat.lTensor_injective_iff_injective R T _

end FaithfulBaseChange

/-- On a field fibre, regularity over an algebraic closure is equivalent to
regularity over the original residue field; the closure stays in the same universe. -/
theorem regular_algebraicClosure_iff {K S : Type*} [Field K] [CommRing S]
    [Algebra K S] (a : S) :
    IsSMulRegular (AlgebraicClosure K ⊗[K] S) ((1 : AlgebraicClosure K) ⊗ₜ[K] a) ↔
      IsSMulRegular S a :=
  regular_tensor_iff (AlgebraicClosure K) a

section FibreBaseChange
variable (K T : Type*) {S : Type*} [CommRing K] [CommRing T] [CommRing S]
  [Algebra R K] [Algebra R T] [Algebra K T] [IsScalarTower R K T] [Algebra R S]

/-- The single tensor describing an extended fibre detects regularity in the
original fibre. The comparison is the canonical cancellation of scalar extension. -/
theorem regular_tensor_tower_iff [Module.FaithfullyFlat K T] (a : S) :
    IsSMulRegular (T ⊗[R] S) ((1 : T) ⊗ₜ[R] a) ↔
      IsSMulRegular (K ⊗[R] S) ((1 : K) ⊗ₜ[R] a) := by
  let e := Algebra.TensorProduct.cancelBaseChange R K T T S
  have he : IsSMulRegular (T ⊗[K] (K ⊗[R] S))
      ((1 : T) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] a)) ↔
        IsSMulRegular (T ⊗[R] S) ((1 : T) ⊗ₜ[R] a) :=
    Equiv.isSMulRegular_congr (e := e.toEquiv) fun x ↦ by
      change e (_ * x) = _ * e x
      rw [map_mul]
      simp [e]
  exact he.symm.trans (regular_tensor_iff T ((1 : K) ⊗ₜ[R] a))

end FibreBaseChange

/-- Passing to an algebraic closure of a prime residue field does not change
regularity of the actual equation in that fibre. -/
theorem regular_geometric_fibre_iff {S : Type*} [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (a : S) :
    IsSMulRegular (AlgebraicClosure p.ResidueField ⊗[R] S)
      ((1 : AlgebraicClosure p.ResidueField) ⊗ₜ[R] a) ↔
        IsSMulRegular (p.Fiber S) ((1 : p.ResidueField) ⊗ₜ[R] a) :=
  regular_tensor_tower_iff p.ResidueField (AlgebraicClosure p.ResidueField) a

section ModelEquivalence
variable {A R S B K : Type*} [CommRing A] [CommRing R] [CommRing S] [CommRing B] [CommRing K]
  [Algebra A R] [Algebra A B] [Algebra R S] [Algebra A K] [Algebra R K]
  [IsScalarTower A R K]

/-- Regularity in a fibre of the limiting algebra is regularity of the actual
chosen equation in the single tensor describing the model fibre. -/
theorem regular_tensor_model_iff (e : R ⊗[A] B ≃ₐ[R] S) (b : B) :
    IsSMulRegular (K ⊗[R] S) ((1 : K) ⊗ₜ[R] e ((1 : R) ⊗ₜ[A] b)) ↔
      IsSMulRegular (K ⊗[A] B) ((1 : K) ⊗ₜ[A] b) := by
  let E : K ⊗[A] B ≃ₐ[K] K ⊗[R] S :=
    (Algebra.TensorProduct.cancelBaseChange A R K K B).symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) e)
  have he : E ((1 : K) ⊗ₜ[A] b) = (1 : K) ⊗ₜ[R] e ((1 : R) ⊗ₜ[A] b) := by
    simp [E, Algebra.TensorProduct.congr_apply]
  exact (Equiv.isSMulRegular_congr (e := E.toEquiv) fun x ↦ by
    change E (_ * x) = _ * E x
    rw [map_mul, he]).symm

end ModelEquivalence

section BaseChange
variable {D R T : Type*} [CommRing D] [CommRing R] [CommRing T]
  [Algebra D R] [Algebra D T]

/-- Base change commutes with the actual principal quotient. -/
def principalTensorQuotientEquiv (a : T) :
    R ⊗[D] (T ⧸ Ideal.span {a}) ≃ₐ[R]
      (R ⊗[D] T) ⧸ Ideal.span {(1 : R) ⊗ₜ[D] a} :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := D) R T R (Ideal.span {a})).trans
    (Ideal.quotientEquivAlgOfEq R (by simp [Ideal.map_span]))

/-- A regular equation with flat quotient stays regular and has flat quotient
after arbitrary scalar extension. Flatness of the scalar extension is not assumed. -/
theorem regular_and_flat_baseChange (a : T) (ha : IsSMulRegular T a)
    [Module.Flat D (T ⧸ Ideal.span {a})] :
    IsSMulRegular (R ⊗[D] T) ((1 : R) ⊗ₜ[D] a) ∧
      Module.Flat R ((R ⊗[D] T) ⧸ Ideal.span {(1 : R) ⊗ₜ[D] a}) := by
  constructor
  · have hf := LinearMap.lTensor_injective_of_exact_of_flat
      (Ideal.Quotient.mkₐ D (Ideal.span {a})).toLinearMap
      (Ideal.Quotient.mkₐ_surjective D _) (LinearMap.mulLeft D a) ha
      (mulLeft_quotient_exact (R := D) a) R
    rwa [lTensor_mulLeft] at hf
  · exact Module.Flat.of_linearEquiv
      (principalTensorQuotientEquiv (D := D) (R := R) a).symm.toLinearEquiv

end BaseChange

section Equivalence
variable {R U V : Type*} [CommRing R] [CommRing U] [CommRing V]
    [Algebra R U] [Algebra R V]

/-- A ring equivalence over the actual base transports the chosen regular
multiplication and flatness of its actual principal quotient. -/
theorem regular_and_flat_of_algEquiv (e : U ≃ₐ[R] V) (a : U)
    (ha : IsSMulRegular U a) [Module.Flat R (U ⧸ Ideal.span {a})] :
    IsSMulRegular V (e a) ∧ Module.Flat R (V ⧸ Ideal.span {e a}) := by
  constructor
  · exact (Equiv.isSMulRegular_congr (e := e.toEquiv)
      (r := a) (s := e a) (fun x ↦ e.map_mul a x)).mp ha
  · let f : (U ⧸ Ideal.span {a}) ≃ₐ[R] (V ⧸ Ideal.span {e a}) :=
      Ideal.quotientEquivAlg _ _ e (by simp [Ideal.map_span])
    exact Module.Flat.of_linearEquiv f.symm.toLinearEquiv

end Equivalence

end Algebra
