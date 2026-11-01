/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.Uniformizer
public import Aglib.RingTheory.Kummer.RootDivisibility
public import Aglib.RingTheory.IntegralClosure.FiniteOverNormal
public import Aglib.FieldTheory.Separable.TensorProductSplitting
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.RingTheory.Etale.Pi

/-! # Normalized root cancellation on the original generic tensor

An embedding of a finite normal separable extension into a specified fraction
field supplies splitting by actual evaluation. Normality of the original base
then identifies the literal integral closure with a finite product of that
base. Specialization to a uniformizer root uses the same root algebra and its
proved DVR structure. This concerns the normalization, never a product
splitting of the original ramified tensor ring.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace integralClosure

universe u v w z

variable (T : Type u) [CommRing T] [IsDomain T] [IsIntegrallyClosed T]
  (K : Type v) [Field K] (L : Type w) [Field L] [Algebra K L]
  [FiniteDimensional K L] [Normal K L] [Algebra.IsSeparable K L]
  (F : Type z) [Field F] [Algebra K F] [Algebra T F] [IsFractionRing T F]

omit [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- One actual embedding into a field splits all minimal polynomials of the
original normal extension there. -/
theorem minpoly_splits_of_normal_embedding (σ : L →ₐ[K] F) (x : L) :
    ((minpoly K x).map (algebraMap K F)).Splits := by
  have h := (Normal.splits (inferInstance : Normal K L) x).map σ.toRingHom
  have hcomp : σ.toRingHom.comp (algebraMap K L) = algebraMap K F :=
    RingHom.ext σ.commutes
  rwa [Polynomial.map_map, hcomp] at h

/-- The normalization of the original generic tensor is a product of copies
of the original normal base; its forward map is induced by actual evaluation. -/
def normalTensorEquivPi (σ : L →ₐ[K] F) :
    integralClosure T (F ⊗[K] L) ≃ₐ[T] ((L →ₐ[K] F) → T) := by
  let c : integralClosure T F ≃ₐ[T] T :=
    IsIntegralClosure.equiv T (integralClosure T F) F T
  let : Module.Finite T (integralClosure T F) :=
    Module.Finite.of_surjective c.symm.toLinearMap c.symm.surjective
  let e := Algebra.IsSeparable.tensorProductEquivPi K L F
    (minpoly_splits_of_normal_embedding K L F σ)
  exact (integralClosure.equivPi T (F ⊗[K] L) (fun _ : L →ₐ[K] F => F)
    (e.restrictScalars T)).trans (AlgEquiv.piCongrRight fun _ => c)

omit [IsDomain T] in
/-- The canonical product comparison preserves each original evaluation in
the specified fraction field. -/
theorem normalTensorEquivPi_apply (σ : L →ₐ[K] F)
    (x : integralClosure T (F ⊗[K] L)) (τ : L →ₐ[K] F) :
    algebraMap T F (normalTensorEquivPi T K L F σ x τ) =
      Algebra.IsSeparable.tensorProductEvaluation K L F (x : F ⊗[K] L) τ := by
  change algebraMap T F
    (IsIntegralClosure.equiv T (integralClosure T F) F T _) = _
  rw [IsIntegralClosure.algebraMap_equiv]
  rfl

omit [IsDomain T] in
/-- Etaleness is a consequence of the proved normalization product, not a
hypothesis on the ramified base-change ring. -/
theorem normalTensor_etale (σ : L →ₐ[K] F) :
    Algebra.Etale T (integralClosure T (F ⊗[K] L)) :=
  Algebra.Etale.of_equiv (normalTensorEquivPi T K L F σ).symm

section IntegralModel

variable (B : Type*) [CommRing B] [Algebra T B] [Algebra.IsIntegral T B]
  [Algebra B (F ⊗[K] L)] [IsScalarTower T B (F ⊗[K] L)]

/-- Normalizing an original integral model inside this same generic tensor
has the same elements. This applies to the original ramified tensor algebra,
without asserting that that algebra itself is a product. -/
def normalIntegralModelTensorEquivPi (σ : L →ₐ[K] F) :
    integralClosure B (F ⊗[K] L) ≃ₐ[T] ((L →ₐ[K] F) → T) :=
  (integralClosure.equivOfIntegral T B (F ⊗[K] L)).trans
    (normalTensorEquivPi T K L F σ)

omit [IsDomain T] in
/-- Integral-model comparison does not alter the original ambient evaluation. -/
theorem normalIntegralModelTensorEquivPi_apply (σ : L →ₐ[K] F)
    (x : integralClosure B (F ⊗[K] L)) (τ : L →ₐ[K] F) :
    algebraMap T F (normalIntegralModelTensorEquivPi T K L F B σ x τ) =
      Algebra.IsSeparable.tensorProductEvaluation K L F (x : F ⊗[K] L) τ :=
  normalTensorEquivPi_apply T K L F σ _ τ

end IntegralModel

end integralClosure

namespace Algebra.Kummer

universe u v w z

section GenericChart

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
  {e N : ℕ} {π : R}
  (K : Type w) [Field K] [Algebra R K] [IsFractionRing R K]
  (F : Type z) [Field F] [Algebra R F]
  [Algebra (RootAlgebra N π) F] [IsScalarTower R (RootAlgebra N π) F]
  [FaithfulSMul R F]

/-- The same generic chart map is linear over the actual extended coefficient
field. The target action is induced by the original fraction-field lift. -/
def rootChartGenericFieldHom (E : RootAlgebra e π ≃ₐ[R] S) (h : e ∣ N) :
    letI : Algebra K F := (rootChartCoefficientHom (R := R) K F).toRingHom.toAlgebra
    K ⊗[R] S →ₐ[K] F := by
  letI : Algebra K F := (rootChartCoefficientHom (R := R) K F).toRingHom.toAlgebra
  refine { (rootChartGenericHom K F E h).toRingHom with commutes' := ?_ }
  intro k
  exact rootChartGenericHom_includeLeft K F E h k

/-- Passing to the coefficient-field-linear presentation does not change the
original map on the literal generic tensor. -/
theorem rootChartGenericFieldHom_apply (E : RootAlgebra e π ≃ₐ[R] S)
    (h : e ∣ N) (x : K ⊗[R] S) :
    rootChartGenericFieldHom K F E h x = rootChartGenericHom K F E h x := rfl

end GenericChart

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (π : R) (hπ : Irreducible π) (N : ℕ) (hN : 0 < N)
  (K : Type v) [Field K] (L : Type w) [Field L] [Algebra K L]
  [FiniteDimensional K L] [Normal K L] [Algebra.IsSeparable K L]
  (F : Type z) [Field F] [Algebra K F]
  [Algebra (RootAlgebra N π) F] [IsFractionRing (RootAlgebra N π) F]

/-- Root cancellation in the literal normalization over the actual uniformizer
root algebra. A strict-Henselian bounded root chart supplies the one embedding;
no splitting or etaleness premise is retained here. -/
def uniformizerRootNormalTensorEquivPi (σ : L →ₐ[K] F) :
    integralClosure (RootAlgebra N π) (F ⊗[K] L) ≃ₐ[RootAlgebra N π]
      ((L →ₐ[K] F) → RootAlgebra N π) := by
  let := uniformizerRoot_isDomain R π hπ N hN
  let := uniformizerRoot_isDiscreteValuationRing R π hπ N hN
  exact integralClosure.normalTensorEquivPi (RootAlgebra N π) K L F σ

include hπ hN in
/-- The same literal root-base normalization is etale, by the constructed
product comparison and the original root algebra's normality. -/
theorem uniformizerRoot_normalTensor_etale (σ : L →ₐ[K] F) :
    Algebra.Etale (RootAlgebra N π)
      (integralClosure (RootAlgebra N π) (F ⊗[K] L)) :=
  Algebra.Etale.of_equiv (uniformizerRootNormalTensorEquivPi R π hπ N hN K L F σ).symm

end Algebra.Kummer
