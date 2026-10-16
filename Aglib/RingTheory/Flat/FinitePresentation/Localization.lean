/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Flat.PrincipalQuotient.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Canonical tensor/localization/quotient comparisons and transport of fibre injections

## Extraction basis

Transferred from `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`
at frozen dirty R5Lab revision `79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.
Source line ranges: 1854–1946, 2458–2591, 2610–2660.
The original rings, modules, canonical maps, universes and hypotheses are retained.
-/

@[expose] public section

noncomputable section
open TensorProduct LinearMap

namespace Algebra.FlatApproximation

variable {A B K M N M' N' : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup K] [Module A K]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  [AddCommGroup M'] [Module A M'] [Module B M'] [IsScalarTower A B M']
  [AddCommGroup N'] [Module A N'] [Module B N'] [IsScalarTower A B N']

/-- Localizing a module map commutes with tensoring over the smaller base. -/
theorem localizedMap_rTensor (U : Submonoid B)
    (jM : M →ₗ[B] M') (jN : N →ₗ[B] N')
    [IsLocalizedModule U jM] [IsLocalizedModule U jN] (f : M →ₗ[B] N) :
    IsLocalizedModule.map U (AlgebraTensorModule.rTensor A K jM)
        (AlgebraTensorModule.rTensor A K jN) (AlgebraTensorModule.rTensor A K f) =
      AlgebraTensorModule.rTensor A K (IsLocalizedModule.map U jM jN f) := by
  apply IsLocalizedModule.linearMap_ext U (AlgebraTensorModule.rTensor A K jM)
    (AlgebraTensorModule.rTensor A K jN)
  rw [IsLocalizedModule.map_comp]
  apply AlgebraTensorModule.ext
  intro m k
  simp

/-- Fibrewise injectivity is preserved on localizing the coefficient-algebra
modules, even when the original base ring is arbitrary. -/
theorem localizedMap_lTensor_injective (U : Submonoid B)
    (jM : M →ₗ[B] M') (jN : N →ₗ[B] N')
    [IsLocalizedModule U jM] [IsLocalizedModule U jN] (f : M →ₗ[B] N)
    (hf : Function.Injective ((f.restrictScalars A).lTensor K)) :
    Function.Injective (((IsLocalizedModule.map U jM jN f).restrictScalars A).lTensor K) := by
  have hf' : Function.Injective (AlgebraTensorModule.rTensor A K f) :=
    (LinearMap.lTensor_inj_iff_rTensor_inj (M := K) (f := f.restrictScalars A)).mp hf
  have h := IsLocalizedModule.map_injective U (AlgebraTensorModule.rTensor A K jM)
    (AlgebraTensorModule.rTensor A K jN) (AlgebraTensorModule.rTensor A K f) hf'
  rw [localizedMap_rTensor] at h
  exact (LinearMap.lTensor_inj_iff_rTensor_inj
    (M := K) (f := (IsLocalizedModule.map U jM jN f).restrictScalars A)).mpr h

end Algebra.FlatApproximation

namespace Algebra.FlatApproximation
variable {A B T K : Type*} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T] [Algebra B T] [IsScalarTower A B T]
  [AddCommGroup K] [Module A K]

/-- The fibre injection remains injective for the actual mapped ideal in a
localization of the coefficient ring. -/
theorem localized_ideal_subtype_lTensor_injective (U : Submonoid B) [IsLocalization U T]
    (I : Ideal B) (hf : Function.Injective ((I.subtype.restrictScalars A).lTensor K)) :
    Function.Injective (((I.map (algebraMap B T)).subtype.restrictScalars A).lTensor K) := by
  let jB := Algebra.linearMap B T
  let J := I.localized' T U jB
  let jI := I.toLocalized' T U jB
  have hmap : IsLocalizedModule.map U jI jB I.subtype = J.subtype.restrictScalars B := by
    apply IsLocalizedModule.linearMap_ext U jI jB
    rw [IsLocalizedModule.map_comp]
    ext x
    rfl
  have h := localizedMap_lTensor_injective (A := A) U jI jB I.subtype hf
  rw [hmap] at h
  have hJ : J = I.map (algebraMap B T) := by
    simp only [J, jB, Submodule.localized'_eq_span, Ideal.map, Ideal.span, Algebra.coe_linearMap]
  change Function.Injective ((J.subtype.restrictScalars A).lTensor K) at h
  rwa [hJ] at h

end Algebra.FlatApproximation

namespace Algebra.FlatApproximation
variable {A D K M N : Type*} [CommRing A] [CommRing D] [Algebra A D]
  [AddCommGroup K] [Module A K] [Module D K] [IsScalarTower A D K]
  [AddCommGroup M] [Module A M] [Module D M] [IsScalarTower A D M]
  [AddCommGroup N] [Module A N] [Module D N] [IsScalarTower A D N]

/-- After localizing the base, the same fibre tensor has the same injectivity. -/
theorem lTensor_injective_over_localization (U : Submonoid A) [IsLocalization U D]
    (f : M →ₗ[D] N) (hf : Function.Injective ((f.restrictScalars A).lTensor K)) :
    Function.Injective (f.lTensor K) := by
  let eM := IsLocalization.moduleTensorEquiv U D K M
  let eN := IsLocalization.moduleTensorEquiv U D K N
  have hc : ((f.restrictScalars A).lTensor K).comp (eM.restrictScalars A).toLinearMap =
      (eN.restrictScalars A).toLinearMap.comp ((f.lTensor K).restrictScalars A) := by
    apply LinearMap.ext
    intro z
    induction z with
    | tmul k m => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x y hxy
  apply eM.injective
  apply hf
  exact (LinearMap.congr_fun hc x).trans
    ((congrArg eN hxy).trans (LinearMap.congr_fun hc y).symm)

end Algebra.FlatApproximation

namespace Algebra.FlatApproximation

variable {A C R B : Type*} [CommRing A] [CommRing C] [CommRing R] [CommRing B]
  [Algebra A C] [Algebra A R] [Algebra C R] [IsScalarTower A C R] [Algebra A B]

/-- Base-changing the actual quotient of a finite coefficient stage recovers
the original quotient presentation. -/
def stageQuotientBaseChangeEquiv (I : Ideal B) :
    R ⊗[C] ((C ⊗[A] B) ⧸ I.map (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B))
      ≃ₐ[R] R ⊗[A] (B ⧸ I) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl (R := R) (A₁ := R))
    (Algebra.TensorProduct.tensorQuotientEquiv (R := A) C B C I).symm).trans
      (Algebra.TensorProduct.cancelBaseChange A C R R (B ⧸ I))

@[simp] theorem stageQuotientBaseChangeEquiv_tmul_mk_tmul
    (I : Ideal B) (r : R) (c : C) (b : B) :
    stageQuotientBaseChangeEquiv (A := A) (C := C) (R := R) I
      (r ⊗ₜ[C] Ideal.Quotient.mk _ (c ⊗ₜ[A] b)) =
      (r * algebraMap C R c) ⊗ₜ[A] Ideal.Quotient.mk I b := by
  simp [stageQuotientBaseChangeEquiv, Algebra.TensorProduct.cancelBaseChange_tmul,
    Algebra.smul_def, mul_comm]

section General
variable {C R Q K S : Type*} [CommRing C] [CommRing R] [CommRing Q]
  [CommRing K] [CommRing S] [Algebra C R] [Algebra C Q] [Algebra C K]
  [Algebra Q K] [IsScalarTower C Q K] [Algebra R S]

/-- The natural map from a model's limiting algebra into the base change of a
localization of the model. -/
def baseChangedLocalizationMap (e : R ⊗[C] Q ≃ₐ[R] S) : S →+* R ⊗[C] K :=
  (Algebra.TensorProduct.lTensor (S := R) R (IsScalarTower.toAlgHom C Q K)).toRingHom.comp
    e.symm.toRingHom

/-- A localization of a model, after scalar extension, is the corresponding
localization of the actual limiting algebra. -/
theorem isLocalization_baseChanged_model (U : Submonoid Q)
    [IsLocalization U K] (e : R ⊗[C] Q ≃ₐ[R] S) :
    letI : Algebra S (R ⊗[C] K) := (baseChangedLocalizationMap e).toAlgebra
    IsLocalization (U.map (e.toRingHom.comp
      (Algebra.TensorProduct.includeRight : Q →ₐ[C] R ⊗[C] Q).toRingHom))
      (R ⊗[C] K) := by
  let : Algebra (R ⊗[C] Q) (R ⊗[C] K) :=
    (Algebra.TensorProduct.lTensor (S := R) R (IsScalarTower.toAlgHom C Q K)).toAlgebra
  have : IsScalarTower R (R ⊗[C] Q) (R ⊗[C] K) :=
    .of_algebraMap_eq (by intro r; simp [RingHom.algebraMap_toAlgebra])
  have hloc := IsLocalization.tensorProduct_tensorProduct_right C R U K
    (by ext; simp [RingHom.algebraMap_toAlgebra])
  let := hloc
  convert IsLocalization.isLocalization_of_base_ringEquiv
    (U.map (Algebra.TensorProduct.includeRight : Q →ₐ[C] R ⊗[C] Q))
    (R ⊗[C] K) e.toRingEquiv using 1
  · exact (Submonoid.map_map U e.toRingEquiv.toMonoidHom
      (Algebra.TensorProduct.includeRight : Q →ₐ[C] R ⊗[C] Q).toMonoidHom).symm
  · rfl

@[simp] theorem baseChangedLocalizationMap_apply
    (e : R ⊗[C] Q ≃ₐ[R] S) (r : R) (q : Q) :
    baseChangedLocalizationMap (K := K) e (e (r ⊗ₜ[C] q)) =
      r ⊗ₜ[C] algebraMap Q K q := by
  simp [baseChangedLocalizationMap]

theorem baseChangedLocalizationMap_isScalarTower (e : R ⊗[C] Q ≃ₐ[R] S) :
    letI : Algebra S (R ⊗[C] K) := (baseChangedLocalizationMap e).toAlgebra
    IsScalarTower R S (R ⊗[C] K) := by
  let : Algebra S (R ⊗[C] K) := (baseChangedLocalizationMap e).toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro r
  simp [RingHom.algebraMap_toAlgebra, baseChangedLocalizationMap]

end General

section LocalizedBase
variable {C D R K : Type*} [CommRing C] [CommRing D] [CommRing R] [CommRing K]
  [Algebra C D] [Algebra C R] [Algebra C K] [Algebra D R] [Algebra D K]
  [IsScalarTower C D R] [IsScalarTower C D K]

/-- Changing a localization base does not change the scalar-extended model. -/
def localizationBaseTensorEquiv (U : Submonoid C) [IsLocalization U D] :
    R ⊗[D] K ≃ₐ[R] R ⊗[C] K :=
  have := IsLocalization.tensorProduct_compatibleSMul U D R K
  Algebra.TensorProduct.equivOfCompatibleSMul C D R R K

@[simp] theorem localizationBaseTensorEquiv_tmul
    (U : Submonoid C) [IsLocalization U D] (r : R) (k : K) :
    localizationBaseTensorEquiv (D := D) U (r ⊗ₜ[D] k) = r ⊗ₜ[C] k := rfl

variable {Q S : Type*} [CommRing Q] [CommRing S] [Algebra C Q] [Algebra Q K]
  [IsScalarTower C Q K] [Algebra R S]

/-- The actual limiting-algebra map into the local-base scalar extension. -/
def localizedBaseChangedLocalizationMap (U : Submonoid C) [IsLocalization U D]
    (e : R ⊗[C] Q ≃ₐ[R] S) : S →+* R ⊗[D] K :=
  (localizationBaseTensorEquiv (D := D) U).symm.toRingHom.comp
    (baseChangedLocalizationMap (K := K) e)

/-- The same intermediate localization after replacing the coefficient base
by its localization. -/
theorem isLocalization_localizedBase_model
    (U : Submonoid C) [IsLocalization U D] (V : Submonoid Q) [IsLocalization V K]
    (e : R ⊗[C] Q ≃ₐ[R] S) :
    letI : Algebra S (R ⊗[D] K) := (localizedBaseChangedLocalizationMap U e).toAlgebra
    IsLocalization (V.map (e.toRingHom.comp
      (Algebra.TensorProduct.includeRight : Q →ₐ[C] R ⊗[C] Q).toRingHom))
      (R ⊗[D] K) := by
  let : Algebra S (R ⊗[C] K) := (baseChangedLocalizationMap e).toAlgebra
  have hloc := isLocalization_baseChanged_model (K := K) V e
  exact (IsLocalization.isLocalization_iff_of_ringEquiv _
    (localizationBaseTensorEquiv (D := D) U).symm.toRingEquiv).mp hloc

@[simp] theorem localizedBaseChangedLocalizationMap_apply
    (U : Submonoid C) [IsLocalization U D]
    (e : R ⊗[C] Q ≃ₐ[R] S) (r : R) (q : Q) :
    localizedBaseChangedLocalizationMap (D := D) (K := K) U e (e (r ⊗ₜ[C] q)) =
      r ⊗ₜ[D] algebraMap Q K q := by
  change (localizationBaseTensorEquiv (D := D) U).symm
    (baseChangedLocalizationMap e (e (r ⊗ₜ[C] q))) = _
  rw [baseChangedLocalizationMap_apply]
  rfl

theorem localizedBaseChangedLocalizationMap_isScalarTower
    (U : Submonoid C) [IsLocalization U D] (e : R ⊗[C] Q ≃ₐ[R] S) :
    letI : Algebra S (R ⊗[D] K) := (localizedBaseChangedLocalizationMap U e).toAlgebra
    IsScalarTower R S (R ⊗[D] K) := by
  let : Algebra S (R ⊗[D] K) := (localizedBaseChangedLocalizationMap U e).toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro r
  simp [RingHom.algebraMap_toAlgebra, localizedBaseChangedLocalizationMap,
    baseChangedLocalizationMap]
  rfl

end LocalizedBase

section QuotientLocalization
variable {C W T : Type*} [CommRing C] [CommRing W] [CommRing T]
  [Algebra C W] [Algebra C T] [Algebra W T] [IsScalarTower C W T]


variable {D R S : Type*} [CommRing D] [CommRing R] [CommRing S]
  [Algebra C D] [Algebra C R] [Algebra D R] [IsScalarTower C D R]
  [Algebra D T] [IsScalarTower C D T] [Algebra R S]

/-- Exact consumer for the Noetherian local model: scalar extension of the
quotient of a localization, over the localized coefficient base, is a
localization of the original limiting algebra. -/
theorem isLocalization_quotient_local_model
    (U : Submonoid C) [IsLocalization U D]
    (V : Submonoid W) [IsLocalization V T] (J : Ideal W)
    (e : R ⊗[C] (W ⧸ J) ≃ₐ[R] S) :
    letI := quotientLocalization_isScalarTower (C := C) (T := T) J
    letI : Algebra S (R ⊗[D] (T ⧸ J.map (algebraMap W T))) :=
      (localizedBaseChangedLocalizationMap U e).toAlgebra
    IsLocalization ((V.map (Ideal.Quotient.mk J)).map (e.toRingHom.comp
      (Algebra.TensorProduct.includeRight : (W ⧸ J) →ₐ[C] R ⊗[C] (W ⧸ J)).toRingHom))
      (R ⊗[D] (T ⧸ J.map (algebraMap W T))) := by
  let := quotientLocalization_isScalarTower (C := C) (T := T) J
  let := quotientLocalization_isLocalization (T := T) V J
  exact isLocalization_localizedBase_model U (V.map (Ideal.Quotient.mk J)) e

end QuotientLocalization

section FurtherLocalization
variable {S U : Type*} [CommRing S] [CommRing U] [Algebra S U]

/-- The actual local ring at a prime is a further localization of any
intermediate localization whose denominators avoid that prime. -/
theorem isLocalization_atPrime_of_intermediate (M : Submonoid S) [IsLocalization M U]
    (Q : Ideal S) [Q.IsPrime] (hM : M ≤ Q.primeCompl) :
    letI := IsLocalization.localizationAlgebraOfSubmonoidLe U (Localization.AtPrime Q)
      M Q.primeCompl hM
    IsScalarTower S U (Localization.AtPrime Q) ∧
      IsLocalization (Q.primeCompl.map (algebraMap S U)) (Localization.AtPrime Q) := by
  let := IsLocalization.localizationAlgebraOfSubmonoidLe U (Localization.AtPrime Q)
    M Q.primeCompl hM
  have ht := IsLocalization.localization_isScalarTower_of_submonoid_le
    U (Localization.AtPrime Q) M Q.primeCompl hM
  exact ⟨ht, IsLocalization.isLocalization_of_submonoid_le
    U (Localization.AtPrime Q) M Q.primeCompl hM⟩

/-- Denominators from the pullback of a prime avoid that prime after mapping. -/
theorem map_primeCompl_comap_le {W : Type*} [CommRing W]
    (f : W →+* S) (Q : Ideal S) [Q.IsPrime] :
    (Q.comap f).primeCompl.map f ≤ Q.primeCompl := by
  rintro _ ⟨x, hx, rfl⟩
  exact hx

end FurtherLocalization

end Algebra.FlatApproximation
