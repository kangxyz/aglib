/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Flat.FinitePresentation.LocalRegularity

/-!
# Finite-stage compatibility and the unrestricted local residue criterion

## Extraction basis

Transferred from `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`
at frozen dirty R5Lab revision `79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.
Source line ranges: 2868–2901, 2909–2950, 2958–3014, 3022–3051.
The original rings, modules, canonical maps, universes and hypotheses are retained.
-/

@[expose] public section

noncomputable section
open TensorProduct LinearMap

namespace Algebra.FlatApproximation

variable {A R B S : Type*} [CommRing A] [CommRing R] [CommRing B] [CommRing S]
  [Algebra A R] [Algebra A B] [Algebra R S] [Algebra A S] [IsScalarTower A R S]

/-- The actual finite-stage quotient presentation of the limiting algebra. -/
def stageModelEquiv (C : Subalgebra A R) (I : Ideal B)
    (e : R ⊗[A] (B ⧸ I) ≃ₐ[R] S) :=
  (stageQuotientBaseChangeEquiv (A := A) (C := C) (R := R) I).trans e

/-- The reconstructed stage equivalence uses exactly the polynomial-stage map
that selected the prime. -/
theorem stageModelEquiv_one_tmul_mk (C : Subalgebra A R) (I : Ideal B)
    (e : R ⊗[A] (B ⧸ I) ≃ₐ[R] S) (w : C ⊗[A] B) :
    stageModelEquiv C I e ((1 : R) ⊗ₜ[C] Ideal.Quotient.mk _ w) = modelStageMap C I e w := by
  induction w using _root_.TensorProduct.inductionOn with
  | tmul c b => simp [stageModelEquiv]
  | add x y hx hy => simp [map_add, tmul_add, hx, hy]

/-- Denominators of the chosen stage prime avoid the actual limiting prime
under the reconstructed quotient presentation. -/
theorem stageModel_denominators_avoid_prime (C : Subalgebra A R) (I : Ideal B)
    (e : R ⊗[A] (B ⧸ I) ≃ₐ[R] S) (Q : Ideal S) [Q.IsPrime] :
    (((Q.comap (modelStageMap C I e)).primeCompl.map (Ideal.Quotient.mk
      (I.map (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B)))).map
      ((stageModelEquiv C I e).toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := C) (A := R)).toRingHom)) ≤
      Q.primeCompl := by
  rintro _ ⟨x, ⟨w, hw, rfl⟩, rfl⟩
  change stageModelEquiv C I e ((1 : R) ⊗ₜ[C] Ideal.Quotient.mk _ w) ∉ Q
  rw [stageModelEquiv_one_tmul_mk]
  exact hw

end Algebra.FlatApproximation

namespace Algebra.FlatApproximation

/-- The generic quotient-model consumer, before specializing its ambient ring
to a finite polynomial presentation. -/
theorem regular_and_flat_atPrime_of_quotient_model
    {C R W S : Type*} [CommRing C] [CommRing R] [CommRing W] [CommRing S]
    [Algebra C R] [Algebra C W] [Algebra R S]
    [IsLocalRing R] [IsNoetherianRing W]
    (q : Ideal W) [q.IsPrime]
    [q.LiesOver ((IsLocalRing.maximalIdeal R).under C)]
    (J : Ideal W) (hJ : J ≤ q) (b : W ⧸ J)
    (e : R ⊗[C] (W ⧸ J) ≃ₐ[R] S)
    (hflat : PrimeQuotientFlat ((IsLocalRing.maximalIdeal R).under C) q J)
    (hb : IsSMulRegular ((R ⧸ IsLocalRing.maximalIdeal R) ⊗[C] (W ⧸ J))
      ((1 : R ⧸ IsLocalRing.maximalIdeal R) ⊗ₜ[C] b))
    (Q : Ideal S) [Q.IsPrime]
    (hdenom : (q.primeCompl.map (Ideal.Quotient.mk J)).map
      (e.toRingHom.comp (Algebra.TensorProduct.includeRight :
        (W ⧸ J) →ₐ[C] R ⊗[C] (W ⧸ J)).toRingHom) ≤ Q.primeCompl) :
    IsSMulRegular (Localization.AtPrime Q)
      (algebraMap S (Localization.AtPrime Q) (e ((1 : R) ⊗ₜ[C] b))) ∧
      Module.Flat R (Localization.AtPrime Q ⧸ Ideal.span
        {algebraMap S (Localization.AtPrime Q) (e ((1 : R) ⊗ₜ[C] b))}) := by
  have hreg := primeQuotient_regular_and_flat_of_residue q J hJ b hflat hb
  let p := (IsLocalRing.maximalIdeal R).under C
  let D := Localization.AtPrime p
  let Wq := Localization.AtPrime q
  let T := Wq ⧸ J.map (algebraMap W Wq)
  let : Algebra D R := (localCoefficientMap (R := R) C).toAlgebra
  have : IsScalarTower C D R := IsScalarTower.of_algebraMap_eq (by
    intro c
    exact (localCoefficientMap_algebraMap C c).symm)
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : IsScalarTower C (W ⧸ J) T := quotientLocalization_isScalarTower J
  have : IsLocalization (q.primeCompl.map (Ideal.Quotient.mk J)) T :=
    quotientLocalization_isLocalization q.primeCompl J
  have hr : IsSMulRegular T (algebraMap (W ⧸ J) T b) := hreg.1
  have : Module.Flat D (T ⧸ Ideal.span {algebraMap (W ⧸ J) T b}) := hreg.2
  exact regular_and_flat_actual_localRing (D := D) (T := T)
    p.primeCompl (q.primeCompl.map (Ideal.Quotient.mk J)) e b hr Q hdenom

end Algebra.FlatApproximation

namespace Algebra.FlatApproximation

variable {A R B S : Type*} [CommRing A] [CommRing R] [CommRing B] [CommRing S]
  [Algebra A R] [Algebra A B] [Algebra R S] [Algebra A S] [IsScalarTower A R S]
  [IsLocalRing R] [IsNoetherianRing A] [Algebra.FiniteType A B]

/-- The finite-stage result applied to an abstract chosen presentation, keeping
polynomial instances out of the loadbearing local argument. -/
theorem regular_and_flat_atPrime_of_stage
    (C : Subalgebra A R) (hC : C.FG) (I : Ideal B)
    (e : R ⊗[A] (B ⧸ I) ≃ₐ[R] S) (b : B)
    (hflat : ∀ (q : Ideal (C ⊗[A] B)) [q.IsPrime] [q.LiesOver (basePrime C)],
      PrimeQuotientFlat (basePrime C) q
        (I.map (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B)))
    (ha : IsSMulRegular ((R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] S)
      ((1 : R ⧸ IsLocalRing.maximalIdeal R) ⊗ₜ[R] e ((1 : R) ⊗ₜ[A] Ideal.Quotient.mk I b)))
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    IsSMulRegular (Localization.AtPrime Q)
      (algebraMap S (Localization.AtPrime Q) (e ((1 : R) ⊗ₜ[A] Ideal.Quotient.mk I b))) ∧
      Module.Flat R (Localization.AtPrime Q ⧸ Ideal.span
        {algebraMap S (Localization.AtPrime Q) (e ((1 : R) ⊗ₜ[A] Ideal.Quotient.mk I b))}) := by
  let W := C ⊗[A] B
  let : CommRing W := inferInstance
  let J : Ideal W := I.map (Algebra.TensorProduct.includeRight : B →ₐ[A] W)
  let B₀ := W ⧸ J
  let : CommRing B₀ := inferInstance
  let : Algebra C B₀ := inferInstance
  let : CommRing (R ⊗[C] B₀) := inferInstance
  let a₀ : B₀ := Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] b)
  let eC := stageModelEquiv C I e
  have heC : eC ((1 : R) ⊗ₜ[C] a₀) = e ((1 : R) ⊗ₜ[A] Ideal.Quotient.mk I b) := by
    change stageModelEquiv C I e ((1 : R) ⊗ₜ[C] Ideal.Quotient.mk _ ((1 : C) ⊗ₜ[A] b)) = _
    rw [stageModelEquiv_one_tmul_mk, modelStageMap_tmul]
    rfl
  let q : Ideal W := Q.comap (modelStageMap C I e)
  obtain ⟨hq, hqp, hJ⟩ := modelStageMap_prime C I e Q
  have : q.IsPrime := hq
  have : q.LiesOver ((IsLocalRing.maximalIdeal R).under C) := by
    rw [← Q.over_def (IsLocalRing.maximalIdeal R)] at hqp
    exact hqp
  have : q.LiesOver (basePrime C) := inferInstanceAs
    (q.LiesOver ((IsLocalRing.maximalIdeal R).under C))
  have : Algebra.FiniteType A C := ⟨(Subalgebra.fg_top C).mpr hC⟩
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
  have : IsNoetherianRing W := Algebra.FiniteType.isNoetherianRing C W
  let K := R ⧸ IsLocalRing.maximalIdeal R
  let : CommRing K := inferInstance
  let : Algebra C K := inferInstance
  have ha₀ : IsSMulRegular (K ⊗[C] B₀) ((1 : K) ⊗ₜ[C] a₀) := by
    apply (regular_tensor_model_iff (A := C) (R := R) (K := K) eC a₀).mp
    rwa [heC]
  have hresult := regular_and_flat_atPrime_of_quotient_model
    (C := C) (R := R) (W := W) q J hJ a₀ eC (hflat q) ha₀ Q
    (stageModel_denominators_avoid_prime C I e Q)
  exact heC ▸ hresult

end Algebra.FlatApproximation

namespace Algebra.FlatApproximation

universe uR uS
variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]

/-- The arbitrary-base local fibrewise regularity criterion at a point over
the closed point of a local base. -/
theorem regular_and_flat_at_prime_of_residue_regular
    [IsLocalRing R] [Algebra.FinitePresentation R S] [Module.Flat R S]
    (a : S) (ha : IsSMulRegular ((R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] S)
      ((1 : R ⧸ IsLocalRing.maximalIdeal R) ⊗ₜ[R] a))
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    IsSMulRegular (Localization.AtPrime Q) (algebraMap S (Localization.AtPrime Q) a) ∧
      Module.Flat R (Localization.AtPrime Q ⧸
        Ideal.span {algebraMap S (Localization.AtPrime Q) a}) := by
  obtain ⟨A, hA, hAR, hlocal, hNoeth, hhom, n, I, b, e, he, C, hC, hflat⟩ :=
    exists_chosen_flat_local_model (R := R) a
  let := hA
  let := hAR
  let := hlocal
  let := hNoeth
  let := hhom
  let : Algebra A S := ((algebraMap R S).comp (algebraMap A R)).toAlgebra
  have : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have hresult := regular_and_flat_atPrime_of_stage
    (A := A) (R := R) (B := MvPolynomial (Fin n) A) (S := S)
    C hC I e b hflat (he.symm ▸ ha) Q
  exact he ▸ hresult

end Algebra.FlatApproximation
