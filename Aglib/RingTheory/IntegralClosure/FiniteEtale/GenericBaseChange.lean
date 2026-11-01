/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.FiniteEtale.LocalFactorGeneric
public import Aglib.RingTheory.Henselian.StrictHenselization.FiniteDecomposition
public import Aglib.RingTheory.DiscreteValuationRing.FractionBaseChange
public import Mathlib.RingTheory.TensorProduct.Pi

/-! # Generic base change with the original normalization factors

The canonical Henselian decomposition, tensorized to the fraction field, uses
exactly the maximal localizations of the original normalization. Further scalar
extension preserves its original generic maps. A separate DVR fraction comparison
identifies the original iterated generic tensor, without replacing either field.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace integralClosure.LocalFactor

variable (R K A : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [Algebra.Etale K A]

local instance : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A

local notation "B" => integralClosure R A
local notation "S" => fun q : MaximalSpectrum B => Localization.AtPrime (MaximalSpectrum.asIdeal q)

include K

/-- The index set consists of the actual maximal primes of the normalization. -/
theorem finite_maximalSpectrum : Finite (MaximalSpectrum B) := by
  let : Module.Finite R B := integralClosure.finite_of_etale R K A
  exact Module.finiteAlgebra_maximalSpectrum_finite R B

/-- The original generic algebra is the product of the literal generic fields
of its original normalization localizations. -/
def genericDecomposition : A ≃ₐ[K] ∀ q : MaximalSpectrum B, K ⊗[R] S q := by
  classical
  let : Module.Finite R B := integralClosure.finite_of_etale R K A
  let : Finite (MaximalSpectrum B) := finite_maximalSpectrum R K A
  let : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  exact (integralClosure.genericFiberEquiv R K A).symm |>.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K)
      ((HenselianLocalRing.finiteAlgebraLocalDecomposition R B).restrictScalars R)).trans
        (Algebra.TensorProduct.piRight R K K S))

/-- Every coordinate is the unchanged generic map, not an arbitrary field isomorphism. -/
@[simp] theorem genericDecomposition_apply (x : A) (q : MaximalSpectrum B) :
    genericDecomposition R K A x q = genericMap R K A q.asIdeal x := by
  obtain ⟨z, rfl⟩ := (integralClosure.genericFiberEquiv R K A).surjective x
  induction z using TensorProduct.inductionOn with
  | tmul k b =>
      simp only [genericDecomposition, genericMap, AlgEquiv.trans_apply,
        AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
      rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

variable (F : Type*) [CommRing F] [Algebra K F]

/-- Further scalar extension distributes over the same finite family of actual
selected generic fields. -/
def baseChangeGenericDecomposition :
    F ⊗[K] A ≃ₐ[F] ∀ q : MaximalSpectrum B, F ⊗[K] (K ⊗[R] S q) := by
  classical
  let : Finite (MaximalSpectrum B) := finite_maximalSpectrum R K A
  let : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  exact (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F)
    (genericDecomposition R K A)).trans
      (Algebra.TensorProduct.piRight K F F (fun q => K ⊗[R] S q))

/-- The scalar-extended coordinate retains the original coefficient and generic map. -/
@[simp] theorem baseChangeGenericDecomposition_tmul (f : F) (x : A)
    (q : MaximalSpectrum B) :
    baseChangeGenericDecomposition R K A F (f ⊗ₜ[K] x) q =
      f ⊗ₜ[K] genericMap R K A q.asIdeal x := by
  classical
  simp [baseChangeGenericDecomposition, Algebra.TensorProduct.congr_apply]

end integralClosure.LocalFactor

namespace IsDiscreteValuationRing

variable (T T' F F' K K' L : Type*)
  [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [CommRing T'] [IsDomain T'] [IsDiscreteValuationRing T']
  [Algebra T T'] [IsLocalHom (algebraMap T T')]
  [Field F] [Algebra T F] [IsFractionRing T F]
  [Field F'] [Algebra T F'] [Algebra T' F'] [IsScalarTower T T' F']
  [IsFractionRing T' F'] [Algebra F F'] [IsScalarTower T F F']
  [CommRing K] [CommRing K'] [CommRing L]
  [Algebra K F] [Algebra K F'] [IsScalarTower K F F']
  [Algebra K K'] [Algebra K' F'] [IsScalarTower K K' F'] [Algebra K L]

/-- Fraction base change and native tensor cancellation compare the original
iterated generic tensor with the original extended-coefficient tensor. -/
def genericTensorBaseChange (hinj : Function.Injective (algebraMap T T')) :
    T' ⊗[T] (F ⊗[K] L) ≃ₐ[T'] F' ⊗[K'] (K' ⊗[K] L) :=
  (fractionBaseChangeAlgEquiv T T' F F' hinj (F ⊗[K] L)).symm.trans
    (((Algebra.TensorProduct.cancelBaseChange K F F' F' L).trans
      (Algebra.TensorProduct.cancelBaseChange K K' F' F' L).symm).restrictScalars T')

/-- The comparison preserves the original root-ring coefficient and old generic
factor. This formula also applies to the original root element. -/
@[simp] theorem genericTensorBaseChange_tmul
    (hinj : Function.Injective (algebraMap T T')) (t : T') (f : F) (l : L) :
    genericTensorBaseChange T T' F F' K K' L hinj (t ⊗ₜ[T] (f ⊗ₜ[K] l)) =
      (algebraMap T' F' t * algebraMap F F' f) ⊗ₜ[K'] (1 ⊗ₜ[K] l) := by
  simp [genericTensorBaseChange, Algebra.smul_def, mul_comm]

end IsDiscreteValuationRing
