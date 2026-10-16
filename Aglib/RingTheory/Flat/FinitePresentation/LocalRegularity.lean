/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Flat.PrincipalQuotient.Local
public import Aglib.RingTheory.Flat.FinitePresentation.Localization
public import Aglib.RingTheory.Flat.FinitePresentation.LocalModel

/-!
# Regularity in the chosen Noetherian local model and algebra local rings

## Extraction basis

Transferred from `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`
at frozen dirty R5Lab revision `79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.
Source line ranges: 2325–2374, 2396–2396, 2403–2450, 2668–2714, 2806–2860.
The original rings, modules, canonical maps, universes and hypotheses are retained.
-/

@[expose] public section

noncomputable section
open TensorProduct LinearMap

namespace Algebra.FlatApproximation
open Module.Flat

variable {C D R B T : Type*} [CommRing C] [CommRing D] [CommRing R]
  [CommRing B] [CommRing T]
  [Algebra C D] [Algebra C R] [Algebra D R] [IsScalarTower C D R]
  [Algebra C B] [Algebra C T] [Algebra B T] [Algebra D T]
  [IsScalarTower C B T] [IsScalarTower C D T]
  [IsLocalRing D] [IsLocalRing R] [IsLocalRing T]
  [IsLocalHom (algebraMap D R)] [IsLocalHom (algebraMap D T)]
  [IsNoetherianRing T] [Module.Flat D T]

/-- Regularity on the limiting residue fibre descends through the field
extension and localization to a flat local Noetherian model. -/
theorem regular_and_flat_local_model
    (V : Submonoid C) [IsLocalization V D]
    (U : Submonoid B) [IsLocalization U T] (a : B)
    (ha : IsSMulRegular ((R ⧸ IsLocalRing.maximalIdeal R) ⊗[C] B)
      ((1 : R ⧸ IsLocalRing.maximalIdeal R) ⊗ₜ[C] a)) :
    IsSMulRegular T (algebraMap B T a) ∧
      Module.Flat D (T ⧸ Ideal.span {algebraMap B T a}) := by
  let K := D ⧸ IsLocalRing.maximalIdeal D
  let L := R ⧸ IsLocalRing.maximalIdeal R
  let : Field K := Ideal.Quotient.field _
  let : Field L := Ideal.Quotient.field _
  let : Algebra K L := (IsLocalRing.ResidueField.map (algebraMap D R)).toAlgebra
  have : IsScalarTower D K L := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let j := Algebra.linearMap B T
  have hmap : IsLocalizedModule.map U j j (LinearMap.mulLeft B a) =
      LinearMap.mulLeft B (algebraMap B T a) := by
    apply IsLocalizedModule.linearMap_ext U j j
    rw [IsLocalizedModule.map_comp]
    ext
    simp [j]
  have ha' : Function.Injective (((LinearMap.mulLeft B a).restrictScalars C).lTensor L) := by
    change Function.Injective ((LinearMap.mulLeft C a).lTensor L)
    rw [lTensor_mulLeft]
    exact ha
  have ht := localizedMap_lTensor_injective (A := C) (K := L) U j j (LinearMap.mulLeft B a) ha'
  rw [hmap] at ht
  have hd : Function.Injective ((LinearMap.mulLeft D (algebraMap B T a)).lTensor L) :=
    lTensor_injective_over_localization (D := D) V (LinearMap.mulLeft D (algebraMap B T a)) ht
  have hr : IsSMulRegular (L ⊗[D] T) ((1 : L) ⊗ₜ[D] algebraMap B T a) := by
    rwa [lTensor_mulLeft] at hd
  have hk := (regular_tensor_tower_iff K L (algebraMap B T a)).mp hr
  apply regular_and_flat_of_residue_regular_noetherian (R := D) (algebraMap B T a)
  rw [lTensor_mulLeft]
  exact hk




end Algebra.FlatApproximation

namespace Algebra.FlatApproximation

/-- A proper quotient of a Noetherian local algebra is again a nonzero local
Noetherian algebra, with the actual quotient structure map local. -/
theorem local_noetherian_quotient_data {D T : Type*} [CommRing D] [CommRing T]
    [Algebra D T] [IsLocalRing T]
    [IsNoetherianRing T] [IsLocalHom (algebraMap D T)]
    (J : Ideal T) (hJ : J ≠ ⊤) :
    Nontrivial (T ⧸ J) ∧ IsLocalRing (T ⧸ J) ∧ IsNoetherianRing (T ⧸ J) ∧
      IsLocalHom (algebraMap D (T ⧸ J)) := by
  have : Nontrivial (T ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (T ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hlocal : IsLocalHom ((Ideal.Quotient.mk J).comp (algebraMap D T)) := inferInstance
  exact ⟨inferInstance, inferInstance, inferInstance, hlocal⟩

/-- Containment in the chosen prime keeps the localized presentation ideal proper. -/
theorem localized_ideal_ne_top_of_le_prime {W T : Type*} [CommRing W] [CommRing T]
    [Algebra W T] (q : Ideal W) [q.IsPrime] [IsLocalization.AtPrime T q]
    [IsLocalRing T] (J : Ideal W) (hJ : J ≤ q) :
    J.map (algebraMap W T) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal T).ne_top
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q T]
  exact Ideal.map_mono hJ

/-- The local quotient selected by the finite-stage prime has every local-ring
instance needed for the Noetherian residue criterion. -/
theorem primeQuotient_local_data {C W : Type*} [CommRing C] [CommRing W]
    [Algebra C W] [IsNoetherianRing W]
    (p : Ideal C) [p.IsPrime] (q : Ideal W) [q.IsPrime] [q.LiesOver p]
    (J : Ideal W) (hJ : J ≤ q) :
    letI := Localization.AtPrime.algebraOfLiesOver p q
    Nontrivial (Localization.AtPrime q ⧸ J.map (algebraMap W (Localization.AtPrime q))) ∧
      IsLocalRing (Localization.AtPrime q ⧸ J.map (algebraMap W (Localization.AtPrime q))) ∧
      IsNoetherianRing (Localization.AtPrime q ⧸ J.map (algebraMap W (Localization.AtPrime q))) ∧
      IsLocalHom (algebraMap (Localization.AtPrime p)
        (Localization.AtPrime q ⧸ J.map (algebraMap W (Localization.AtPrime q)))) := by
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    rw [Localization.AtPrime.algebraMap_eq p q]
    exact Localization.isLocalHom_localRingHom _ _ _ _
  exact local_noetherian_quotient_data (D := Localization.AtPrime p)
    (J.map (algebraMap W (Localization.AtPrime q)))
    (localized_ideal_ne_top_of_le_prime q J hJ)

end Algebra.FlatApproximation

namespace Algebra.FlatApproximation

/-- Regularity and flatness of the principal quotient in the actual localized
presentation quotient. -/
def PrimeQuotientRegularFlat {C W : Type*} [CommRing C] [CommRing W] [Algebra C W]
    (p : Ideal C) [p.IsPrime] (q : Ideal W) [q.IsPrime] [q.LiesOver p]
    (J : Ideal W) (b : W ⧸ J) : Prop :=
  letI := Localization.AtPrime.algebraOfLiesOver p q
  let T := Localization.AtPrime q ⧸ J.map (algebraMap W (Localization.AtPrime q))
  IsSMulRegular T (algebraMap (W ⧸ J) T b) ∧
    Module.Flat (Localization.AtPrime p) (T ⧸ Ideal.span {algebraMap (W ⧸ J) T b})

/-- Residue-fibre regularity of the limiting equation forces regularity and
flat principal quotient in the selected Noetherian local presentation model. -/
theorem primeQuotient_regular_and_flat_of_residue
    {C R W : Type*} [CommRing C] [CommRing R] [CommRing W]
    [Algebra C R] [Algebra C W] [IsLocalRing R] [IsNoetherianRing W]
    (q : Ideal W) [q.IsPrime]
    [q.LiesOver ((IsLocalRing.maximalIdeal R).under C)]
    (J : Ideal W) (hJ : J ≤ q) (b : W ⧸ J)
    (hflat : PrimeQuotientFlat ((IsLocalRing.maximalIdeal R).under C) q J)
    (hb : IsSMulRegular ((R ⧸ IsLocalRing.maximalIdeal R) ⊗[C] (W ⧸ J))
      ((1 : R ⧸ IsLocalRing.maximalIdeal R) ⊗ₜ[C] b)) :
    PrimeQuotientRegularFlat ((IsLocalRing.maximalIdeal R).under C) q J b := by
  let p := (IsLocalRing.maximalIdeal R).under C
  let D := Localization.AtPrime p
  let Wq := Localization.AtPrime q
  let T := Wq ⧸ J.map (algebraMap W Wq)
  let : Algebra D R := (localCoefficientMap (R := R) C).toAlgebra
  have : IsScalarTower C D R := IsScalarTower.of_algebraMap_eq (by
    intro c
    exact (localCoefficientMap_algebraMap C c).symm)
  have : IsLocalHom (algebraMap D R) := localCoefficientMap_isLocal C
  let := Localization.AtPrime.algebraOfLiesOver p q
  obtain ⟨hnontriv, hlocal, hNoeth, hhom⟩ := primeQuotient_local_data p q J hJ
  let := hnontriv
  let := hlocal
  let := hNoeth
  let := hhom
  have : Module.Flat D T := hflat
  have : IsScalarTower C (W ⧸ J) T := quotientLocalization_isScalarTower J
  have : IsLocalization (q.primeCompl.map (Ideal.Quotient.mk J)) T :=
    quotientLocalization_isLocalization q.primeCompl J
  exact regular_and_flat_local_model (D := D) (R := R)
    p.primeCompl (q.primeCompl.map (Ideal.Quotient.mk J)) b hb

end Algebra.FlatApproximation

namespace Algebra.FlatApproximation

variable {C D R B T S : Type*}
  [CommRing C] [CommRing D] [CommRing R] [CommRing B] [CommRing T] [CommRing S]
  [Algebra C D] [Algebra C R] [Algebra C B] [Algebra C T]
  [Algebra D R] [Algebra D T] [Algebra B T]
  [IsScalarTower C D R] [IsScalarTower C D T] [IsScalarTower C B T]
  [Algebra R S]

/-- Regularity and quotient flatness on the constructed local model transport
to the actual local ring of the original algebra. All maps of the chosen
element are the canonical presentation, scalar-extension, and localization maps. -/
theorem regular_and_flat_actual_localRing
    (U : Submonoid C) [IsLocalization U D]
    (V : Submonoid B) [IsLocalization V T]
    (e : R ⊗[C] B ≃ₐ[R] S) (a : B)
    (ha : IsSMulRegular T (algebraMap B T a))
    [Module.Flat D (T ⧸ Ideal.span {algebraMap B T a})]
    (Q : Ideal S) [Q.IsPrime]
    (hV : V.map (e.toRingHom.comp
      (Algebra.TensorProduct.includeRight : B →ₐ[C] R ⊗[C] B).toRingHom) ≤ Q.primeCompl) :
    IsSMulRegular (Localization.AtPrime Q)
      (algebraMap S (Localization.AtPrime Q) (e ((1 : R) ⊗ₜ[C] a))) ∧
      Module.Flat R (Localization.AtPrime Q ⧸ Ideal.span
        {algebraMap S (Localization.AtPrime Q) (e ((1 : R) ⊗ₜ[C] a))}) := by
  let W := R ⊗[D] T
  let M : Submonoid S := V.map (e.toRingHom.comp
    (Algebra.TensorProduct.includeRight : B →ₐ[C] R ⊗[C] B).toRingHom)
  let : Algebra S W := (localizedBaseChangedLocalizationMap (D := D) U e).toAlgebra
  have : IsLocalization M W := isLocalization_localizedBase_model U V e
  have : IsScalarTower R S W := localizedBaseChangedLocalizationMap_isScalarTower U e
  let : Algebra W (Localization.AtPrime Q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe W (Localization.AtPrime Q) M Q.primeCompl hV
  have ht := isLocalization_atPrime_of_intermediate (U := W) M Q hV
  have : IsScalarTower S W (Localization.AtPrime Q) := ht.1
  have : IsLocalization (Q.primeCompl.map (algebraMap S W)) (Localization.AtPrime Q) := ht.2
  have : IsScalarTower R W (Localization.AtPrime Q) := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    rw [IsScalarTower.algebraMap_apply R S W,
      ← IsScalarTower.algebraMap_apply S W (Localization.AtPrime Q),
      ← IsScalarTower.algebraMap_apply R S (Localization.AtPrime Q)]
  have hchosen : algebraMap S W (e ((1 : R) ⊗ₜ[C] a)) =
      (1 : R) ⊗ₜ[D] algebraMap B T a :=
    localizedBaseChangedLocalizationMap_apply U e 1 a
  have hfinal : algebraMap W (Localization.AtPrime Q)
      ((1 : R) ⊗ₜ[D] algebraMap B T a) =
      algebraMap S (Localization.AtPrime Q) (e ((1 : R) ⊗ₜ[C] a)) := by
    rw [← hchosen, ← IsScalarTower.algebraMap_apply S W (Localization.AtPrime Q)]
  have hresult := regular_and_flat_baseChange_localization
    (D := D) (R := R) (V := Localization.AtPrime Q)
    (Q.primeCompl.map (algebraMap S W)) (algebraMap B T a) ha
  exact hfinal ▸ hresult

end Algebra.FlatApproximation
