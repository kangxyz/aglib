/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.FiniteEtale.LocalFactor
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # The original generic field of the selected local normalization

The literal tensor generic fibre of the selected prime localization is a field.
The original generic algebra maps onto it by tensoring the original localization
map. The same local ring is its integral closure over the original DVR; no
replacement field component is selected.
-/

@[expose] public noncomputable section

open scoped TensorProduct nonZeroDivisors

namespace integralClosure.LocalFactor

universe u v w

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
  (A : Type w) [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [Algebra.Etale K A]
  (q : Ideal (integralClosure R A)) [q.IsMaximal]

local notation "C₀" => integralClosure R A
local notation "S₀" => Localization.AtPrime q
local notation "L₀" => K ⊗[R] S₀

local instance : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A

/-- The selected local factor acts through the right factor of its generic tensor. -/
local instance genericRightTensorAlgebra : Algebra S₀ L₀ := Algebra.TensorProduct.rightAlgebra

include K

omit [HenselianLocalRing R] in
/-- The original base map into the selected local factor is injective. -/
theorem algebraMap_injective : Function.Injective (algebraMap R S₀) := by
  let : IsDomain S₀ := localizationAtPrime_isDomain R K A q
  let : Module.Flat R C₀ := integralClosure.flat_of_etale R K A
  let : Module.Flat R S₀ := Module.Flat.trans R C₀ S₀
  let : Module.IsTorsionFree R S₀ := Module.Flat.isTorsionFree
  let : @FaithfulSMul R S₀ (inferInstance : Algebra R S₀).toSMul :=
    Module.IsTorsionFree.to_faithfulSMul
  exact FaithfulSMul.algebraMap_injective R S₀

/-- The localization denominators are nonzero in the same selected factor. -/
theorem denominators_le_nonZeroDivisors :
    Algebra.algebraMapSubmonoid S₀ R⁰ ≤ S₀⁰ := by
  let : IsDomain S₀ := localizationAtPrime_isDomain R K A q
  rintro _ ⟨r, hr, rfl⟩
  apply mem_nonZeroDivisors_of_ne_zero
  exact (map_ne_zero_iff _ (algebraMap_injective R K A q)).mpr
    (nonZeroDivisors.ne_zero hr)

omit [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Algebra K A] [IsScalarTower R K A] [Algebra.Etale K A] in
/-- The original tensor is the localization by the original nonzero base elements. -/
theorem generic_isLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid S₀ R⁰) L₀ :=
  IsLocalization.tensorRight (R := R) (S := S₀) (A := K) R⁰

/-- The literal tensor generic fibre is a domain. -/
theorem generic_isDomain : IsDomain L₀ := by
  let : IsDomain S₀ := localizationAtPrime_isDomain R K A q
  let := generic_isLocalization R K A q
  exact IsLocalization.isDomain_of_le_nonZeroDivisors L₀
    (denominators_le_nonZeroDivisors R K A q)

/-- The literal tensor generic fibre is a field, not a selected product component. -/
@[instance_reducible] def genericField : Field L₀ := by
  let := generic_isDomain R K A q
  let : Module.Finite R S₀ := localizationAtPrime_finite R K A q
  let : Module.Finite K L₀ := inferInstance
  have hf : IsField L₀ := isField_of_isIntegral_of_isField' (Field.toIsField K)
  exact hf.toField


/-- The same tensor field is the fraction field of the original selected localization. -/
theorem generic_isFractionRing : IsFractionRing S₀ L₀ := by
  let : IsDomain S₀ := localizationAtPrime_isDomain R K A q
  let : Field L₀ := genericField R K A q
  let := generic_isLocalization R K A q
  apply IsLocalization.of_le (Algebra.algebraMapSubmonoid S₀ R⁰) S₀⁰
    (denominators_le_nonZeroDivisors R K A q)
  intro s hs
  apply isUnit_iff_ne_zero.mpr
  apply (map_ne_zero_iff _ (IsLocalization.injective L₀
    (denominators_le_nonZeroDivisors R K A q))).mpr
  exact nonZeroDivisors.ne_zero hs

/-- The original selected local ring is the integral closure in its literal
fraction field. Its finiteness and DVR normality are supplied, not assumed. -/
theorem generic_isIntegralClosure : IsIntegralClosure S₀ R L₀ := by
  let : IsDomain S₀ := localizationAtPrime_isDomain R K A q
  let : IsDiscreteValuationRing S₀ := localizationAtPrime_isDiscreteValuationRing R K A q
  let : Module.Finite R S₀ := localizationAtPrime_finite R K A q
  let := generic_isFractionRing R K A q
  exact IsIntegralClosure.of_isIntegrallyClosed S₀ R L₀

/-- The original generic algebra maps to the original tensor generic fibre by
inverting its native generic-fibre equivalence and tensoring the localization map. -/
def genericMap : A →ₐ[K] L₀ :=
  (Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom R C₀ S₀)).comp
    (integralClosure.genericFiberEquiv R K A).symm.toAlgHom

omit [IsDiscreteValuationRing R] [HenselianLocalRing R] in
/-- The actual generic map retains the original coefficient/localization equation. -/
theorem genericMap_mul (k : K) (b : C₀) :
    genericMap R K A q (algebraMap K A k * (b : A)) = k ⊗ₜ[R] algebraMap C₀ S₀ b := by
  rw [← integralClosure.genericFiberEquiv_tmul R K A k b]
  simp only [genericMap, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rfl

/-- The original generic algebra surjects onto this same field, since the
original Henselian localization map is surjective. -/
theorem genericMap_surjective : Function.Surjective (genericMap R K A q) :=
  (Algebra.TensorProduct.map_surjective (AlgHom.id K K) (IsScalarTower.toAlgHom R C₀ S₀)
    Function.surjective_id
    (localizationAtPrime_algebraMap_surjective R K A q)).comp
      (integralClosure.genericFiberEquiv R K A).symm.surjective

/-- The original generic field is finite over the original fraction field. -/
theorem generic_finite : Module.Finite K L₀ := by
  let : Module.Finite R S₀ := localizationAtPrime_finite R K A q
  infer_instance

/-- The original generic field is etale over the original fraction field,
using the original surjection from the original etale generic algebra. -/
theorem generic_etale : Algebra.Etale K L₀ := by
  let : Field L₀ := genericField R K A q
  let : Module.Finite K L₀ := generic_finite R K A q
  let : Algebra.FormallyUnramified K L₀ := Algebra.FormallyUnramified.of_surjective
    (genericMap R K A q) (genericMap_surjective R K A q)
  let : Algebra.FiniteType K L₀ := Module.Finite.finiteType L₀
  let : Algebra.EssFiniteType K L₀ := Algebra.EssFiniteType.of_finiteType K L₀
  let : Algebra.FinitePresentation K L₀ := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.IsSeparable K L₀ := Algebra.FormallyUnramified.isSeparable K L₀
  let : Algebra.FormallyEtale K L₀ := Algebra.FormallyEtale.of_isSeparable K L₀
  exact ⟨inferInstance, inferInstance⟩

end integralClosure.LocalFactor
