/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.RegularParameter
public import Aglib.RingTheory.Kummer.Evaluation
public import Aglib.RingTheory.RegularLocalRing.Normal
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! # Recognition of an original regular-parameter root normalization

The specified root evaluates the literal root algebra into the original field.
Its fraction-ring property is constructed using the actual coefficient
localization and the given field generation. Regular-parameter normality then
identifies the same root algebra with the literal integral closure. No additional
fraction-field model, binomial irreducibility premise, or normalization comparison
is supplied.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

namespace Algebra.Kummer

universe u v w

section Generic

variable (R : Type u) (K : Type v) (L : Type w)
  [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  (N : ℕ) (hN : 0 < N) (f : R) (β : L) (hpow : β ^ N = algebraMap R L f)
  (hgen : IntermediateField.adjoin K {β} = ⊤)

local notation "D" => RootAlgebra N f
local notation "U" => RootAlgebra N (algebraMap R K f)
local notation "S" => Algebra.algebraMapSubmonoid D (nonZeroDivisors R)

include hpow in
omit [IsDomain R] [IsFractionRing R K] in
/-- The original root equation over the original coefficient fraction field. -/
theorem rootEvaluation_fraction_pow : β ^ N = algebraMap K L (algebraMap R K f) :=
  hpow.trans (IsScalarTower.algebraMap_apply R K L f)

/-- The same root evaluates the actual coefficient-localized root algebra. -/
def rootEvaluationGeneric : U →ₐ[K] L :=
  rootEvaluation K L N (algebraMap R K f) β
    (rootEvaluation_fraction_pow R K L N f β hpow)

omit [IsDomain R] [IsFractionRing R K] in
/-- Coefficient localization commutes with the original root evaluation. -/
theorem rootEvaluationGeneric_comp :
    ((rootEvaluationGeneric R K L N f β hpow).restrictScalars R).comp
      (rootBaseChangeHom K N f) = rootEvaluation R L N f β hpow := by
  apply AdjoinRoot.algHom_ext
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, rootBaseChangeHom_root,
    rootEvaluationGeneric, rootEvaluation_root]

include hN in
/-- Original coefficient denominators stay regular in the literal domain root algebra. -/
theorem root_denominators_regular [IsDomain D] : S ≤ nonZeroDivisors D := by
  have hinj : Function.Injective (algebraMap R D) :=
    AdjoinRoot.of.injective_of_monic_of_degree_pos (monic_X_pow_sub_C f hN.ne') (by
      rw [degree_X_pow_sub_C hN]
      exact_mod_cast hN)
  exact map_le_nonZeroDivisors_of_injective _ hinj le_rfl

/-- The original generic evaluation is bijective: the localized root algebra
is a finite domain over the coefficient field, and the specified root generates. -/
def rootEvaluationGenericEquiv [IsDomain D] : U ≃ₐ[K] L := by
  let : Algebra D U := rootBaseChangeAlgebra K N f
  let : IsLocalization S U := rootBaseChange_isLocalization K N f (nonZeroDivisors R)
  let : IsDomain U := IsLocalization.isDomain_of_le_nonZeroDivisors U
    (root_denominators_regular R N hN f)
  let : Module.Finite K U := root_finite N hN (algebraMap R K f)
  let φ := rootEvaluationGeneric R K L N f β hpow
  have hinj : Function.Injective φ := by
    apply (injective_iff_map_eq_zero φ).mpr
    intro x hx
    by_contra hzero
    exact (((_root_.IsIntegral.of_finite K x).isUnit hzero).map φ).ne_zero hx
  have hβ : IsIntegral K β :=
    ⟨X ^ N - C (algebraMap R K f), monic_X_pow_sub_C _ hN.ne', by
      simp [rootEvaluation_fraction_pow R K L N f β hpow]⟩
  have hadjoin : Algebra.adjoin K {β} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hβ.isAlgebraic, hgen]
    rfl
  have hsurj : Function.Surjective φ := by
    apply (AlgHom.range_eq_top φ).mp
    apply top_unique
    rw [← hadjoin]
    apply Algebra.adjoin_le
    intro x hx
    have hx' : x = β := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨AdjoinRoot.root (rootPolynomial N (algebraMap R K f)),
      rootEvaluation_root K L N (algebraMap R K f) β _⟩
  exact AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩

include K hN hgen in
/-- The literal root evaluation is a fraction map into the original generated
field. Its source-domain condition is supplied by regular-parameter regularity. -/
theorem rootEvaluation_isFractionRing [IsDomain D] :
    letI := rootEvaluationAlgebra R L N f β hpow
    IsFractionRing D L := by
  let := rootEvaluationAlgebra R L N f β hpow
  let : Algebra D U := rootBaseChangeAlgebra K N f
  let : IsLocalization S U := rootBaseChange_isLocalization K N f (nonZeroDivisors R)
  let e : U ≃ₐ[D] L :=
    { (rootEvaluationGenericEquiv R K L N hN f β hpow hgen).toRingEquiv with
      commutes' x := AlgHom.congr_fun (rootEvaluationGeneric_comp R K L N f β hpow) x }
  let : IsLocalization S L := IsLocalization.isLocalization_of_algEquiv S e
  have hS := root_denominators_regular R N hN f
  apply IsLocalization.of_le S (nonZeroDivisors D) hS
  intro x hx
  apply IsUnit.mk0
  intro hz
  apply mem_nonZeroDivisors_iff_ne_zero.mp hx
  apply IsLocalization.injective L hS
  simpa using hz

end Generic

section RegularParameter

variable (R : Type u) (K : Type v) (L : Type w)
  [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  (N : ℕ) (hN : 0 < N) (f : R) (hf : f ∈ maximalIdeal R)
  (hreg : IsSMulRegular R f) [IsRegularLocalRing (R ⧸ Ideal.span {f})]
  (β : L) (hpow : β ^ N = algebraMap R L f)
  (hgen : IntermediateField.adjoin K {β} = ⊤)

local notation "D" => RootAlgebra N f

include K hN hf hreg hgen in
/-- Regularity identifies the original root algebra as the integral closure
inside the original field with its specified root-evaluation action. -/
theorem parameterRoot_isIntegralClosure :
    letI := rootEvaluationAlgebra R L N f β hpow
    IsIntegralClosure D R L := by
  let := rootEvaluationAlgebra R L N f β hpow
  let : IsScalarTower R D L := IsScalarTower.of_algHom (rootEvaluation R L N f β hpow)
  let : IsRegularLocalRing D := parameterRoot_isRegularLocalRing R f hf N hN hreg
  let : IsDomain D := IsRegularLocalRing.isDomain_of_regularLocal D
  let : IsIntegrallyClosed D := IsRegularLocalRing.isIntegrallyClosed_of_regularLocal D
  let : Module.Finite R D := root_finite N hN f
  let : IsFractionRing D L := rootEvaluation_isFractionRing R K L N hN f β hpow hgen
  exact IsIntegralClosure.of_isIntegrallyClosed D R L

/-- The regular-parameter root algebra is the literal normalization in the
unchanged field. No normalization or fraction-ring comparison is an input. -/
def parameterRootIntegralClosureEquiv : D ≃ₐ[R] integralClosure R L := by
  letI := rootEvaluationAlgebra R L N f β hpow
  letI : IsScalarTower R D L := IsScalarTower.of_algHom (rootEvaluation R L N f β hpow)
  letI : IsIntegralClosure D R L :=
    parameterRoot_isIntegralClosure R K L N hN f hf hreg β hpow hgen
  exact IsIntegralClosure.equiv R D L (integralClosure R L)

/-- The normalization equivalence preserves every original ambient field value. -/
@[simp] theorem parameterRootIntegralClosureEquiv_coe (x : D) :
    (parameterRootIntegralClosureEquiv R K L N hN f hf hreg β hpow hgen x : L) =
      rootEvaluation R L N f β hpow x := by
  let := rootEvaluationAlgebra R L N f β hpow
  let : IsScalarTower R D L := IsScalarTower.of_algHom (rootEvaluation R L N f β hpow)
  let : IsIntegralClosure D R L :=
    parameterRoot_isIntegralClosure R K L N hN f hf hreg β hpow hgen
  exact IsIntegralClosure.algebraMap_equiv R D L (integralClosure R L) x

/-- In particular, the original quotient root has exactly the specified value. -/
theorem parameterRootIntegralClosureEquiv_root :
    (parameterRootIntegralClosureEquiv R K L N hN f hf hreg β hpow hgen
      (AdjoinRoot.root (rootPolynomial N f)) : L) = β := by
  rw [parameterRootIntegralClosureEquiv_coe, rootEvaluation_root]

/-- The comparison is linear over the unchanged coefficient ring. -/
theorem parameterRootIntegralClosureEquiv_algebraMap (r : R) :
    parameterRootIntegralClosureEquiv R K L N hN f hf hreg β hpow hgen
      (algebraMap R D r) = algebraMap R (integralClosure R L) r :=
  (parameterRootIntegralClosureEquiv R K L N hN f hf hreg β hpow hgen).commutes r

end RegularParameter

end Algebra.Kummer
