/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.GenericTensorResidue
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Ideal

/-! # The original centre after the actual generic parameter extension

The tensor source is a localization of the original polynomial source. Restricting
the actual generic residue point to that source computes its kernel, so no new
centre is silently substituted for the extension of the original one.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace GenericParameterCentre

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (ι : Type*) (p : R) [Fact (Irreducible p)]
variable {B : Type*} [CommRing B] [Algebra R B]

attribute [local instance] MvPolynomial.algebraMvPolynomial

local notation "P" => MvPolynomial ι R
local notation "Q" => MvPolynomial ι B
local notation "R₁" => ParameterLocalization.Ring R ι p
local notation "A" => B ⊗[R] R₁
local notation "T" => Q ⊗[P] R₁

/-- The native polynomial pushout identifies the two actual tensor descriptions. -/
def polynomialTensorEquiv : T ≃ₐ[B] A :=
  Algebra.IsPushout.cancelBaseChangeAlg R B P Q R₁

/-- The original polynomial source map into the actual parameter tensor source. -/
def polynomialMap : Q →+* A :=
  (polynomialTensorEquiv R ι p).toRingHom.comp Algebra.TensorProduct.includeLeftRingHom

/-- Original coefficients are unchanged by the polynomial-source description. -/
@[simp] theorem polynomialMap_C (b : B) :
    polynomialMap R ι p (MvPolynomial.C b) =
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] A) b := by
  change polynomialTensorEquiv R ι p (algebraMap B T b) = algebraMap B A b
  exact (polynomialTensorEquiv R ι p).commutes b

/-- The source variables are the very same parameter variables in the right tensor factor. -/
@[simp] theorem polynomialMap_X (i : ι) :
    polynomialMap R ι p (MvPolynomial.X i) =
      (Algebra.TensorProduct.includeRight : R₁ →ₐ[R] A)
        (algebraMap P R₁ (MvPolynomial.X i)) := by
  change polynomialTensorEquiv R ι p ((MvPolynomial.X i : Q) ⊗ₜ[P] (1 : R₁)) = _
  have hx : (MvPolynomial.X i : Q) = algebraMap P Q (MvPolynomial.X i) := by
    simp only [MvPolynomial.algebraMap_def, MvPolynomial.map_X]
  rw [hx, Algebra.TensorProduct.tmul_one_eq_one_tmul,
    polynomialTensorEquiv, Algebra.IsPushout.cancelBaseChangeAlg_tmul]
  rfl

/-- The actual polynomial map gives the source its genuine localization structure. -/
theorem isLocalization_polynomialMap :
    letI := (polynomialMap (B := B) R ι p).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid Q
      (ParameterLocalization.parameterIdeal R ι p).primeCompl) A := by
  let : Algebra Q A := (polynomialMap R ι p).toAlgebra
  let e : T ≃ₐ[Q] A :=
    { (polynomialTensorEquiv R ι p).toRingEquiv with commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv
    (Algebra.algebraMapSubmonoid Q (ParameterLocalization.parameterIdeal R ι p).primeCompl) e

variable (K : Type*) [Field K] [Algebra (ResidueField R) K]

attribute [local instance] GenericParameterField.fractionAlgebra

/-- The centre field retains the original coefficient action through the given
residue-field algebra and the original residue map. -/
local instance genericCentreResidueAlgebra : Algebra R K :=
  ((algebraMap (ResidueField R) K).comp (residue R)).toAlgebra
local instance genericCentreResidueTower : IsScalarTower R (ResidueField R) K :=
  IsScalarTower.of_algebraMap_eq' rfl

local notation "L" => FractionRing (MvPolynomial ι K)

variable (g : B →ₐ[R] K)

/-- On the actual polynomial source, the tensor residue point is the original
coefficient map followed by the injective map into the generic fraction field. -/
theorem tensorPoint_comp_polynomialMap :
    (tensorPoint R K ι p g).toRingHom.comp (polynomialMap R ι p) =
      (algebraMap (MvPolynomial ι K) L).comp (MvPolynomial.map g.toRingHom) := by
  apply MvPolynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply, polynomialMap_C, MvPolynomial.map_C]
    change tensorPoint R K ι p g
      ((Algebra.TensorProduct.includeLeft : B →ₐ[R] A) b) =
      algebraMap (MvPolynomial ι K) L (MvPolynomial.C (g b))
    rw [tensorPoint_includeLeft]
    exact IsScalarTower.algebraMap_apply K (MvPolynomial ι K) L (g b)
  · intro i
    simp only [RingHom.comp_apply, polynomialMap_X, MvPolynomial.map_X]
    have hr := DFunLike.congr_fun (tensorPoint_includeRight R K ι p g)
      (algebraMap P R₁ (MvPolynomial.X i))
    change tensorPoint R K ι p g
      ((Algebra.TensorProduct.includeRight : R₁ →ₐ[R] A)
        (algebraMap P R₁ (MvPolynomial.X i))) = _ at hr
    change tensorPoint R K ι p g
      ((Algebra.TensorProduct.includeRight : R₁ →ₐ[R] A)
        (algebraMap P R₁ (MvPolynomial.X i))) =
      algebraMap (MvPolynomial ι K) L (MvPolynomial.X i)
    rw [hr, RingHom.comp_apply, parameterResidue_X]
    exact GenericParameterField.fractionMap_X (ResidueField R) K ι i

/-- The centre of the actual tensor residue point is precisely the extension of
its original source centre, even when the original point is not surjective. -/
theorem ker_tensorPoint :
    RingHom.ker (tensorPoint R K ι p g).toRingHom =
      (RingHom.ker g.toRingHom).map
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] A).toRingHom := by
  let : Algebra Q A := (polynomialMap R ι p).toAlgebra
  let M := Algebra.algebraMapSubmonoid Q
    (ParameterLocalization.parameterIdeal R ι p).primeCompl
  let : IsLocalization M A := isLocalization_polynomialMap R ι p
  have hk : (RingHom.ker (tensorPoint R K ι p g).toRingHom).under Q =
      (RingHom.ker g.toRingHom).map MvPolynomial.C := by
    change RingHom.ker ((tensorPoint R K ι p g).toRingHom.comp
      (polynomialMap R ι p)) = _
    rw [tensorPoint_comp_polynomialMap, RingHom.ker_comp_of_injective _
      (IsFractionRing.injective (MvPolynomial ι K) L), MvPolynomial.ker_map]
  rw [← IsLocalization.map_under M A (RingHom.ker (tensorPoint R K ι p g).toRingHom),
    hk, Ideal.map_map]
  congr 1
  ext b
  exact polynomialMap_C R ι p b

end GenericParameterCentre
