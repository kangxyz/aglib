/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Descent.FormalGluing.FiniteModification
public import Aglib.RingTheory.IntegralClosure.FlatBaseChange
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Normalization with a supported conductor under faithfully flat base change

Let `R → S` be a faithfully flat map of domains. Suppose a finitely generated
ideal `J` contains a nonzero element, the original map identifies `R/J` with
`S/JS`, and `JS` multiplies the actual normalization of `S` into `S`.
Then the original `integralClosure.flatBaseChangeHom` is bijective. Its algebra
equivalence retains the original tensor and total-fraction maps. Finiteness
of the upper normalization descends without a Noetherian hypothesis.

The proof reuses the actual regular-conductor model and its proved finite
cross-relation comparison. Each element of that model maps to the original
fraction ring of `R`; faithful-flat integrality descent puts it in the actual
normalization of `R`. The final surjectivity assertion concerns the existing
normalization map, not a chosen replacement algebra equivalence.
-/

@[expose] public noncomputable section

open scoped TensorProduct nonZeroDivisors

universe u v w z

namespace Algebra.Descent.FormalGluing

section IntegralDescent

variable {R : Type u} {S : Type v} {A : Type w} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] [Module.FaithfullyFlat R S]

/-- Integrality of an original unit tensor descends by faithful flatness.
The proof constructs the scalar extension of the original monogenic algebra,
proves its finiteness from the integral tensor generator, and descends that
module finiteness. No integrality or descent datum is assumed on the source. -/
theorem isIntegral_of_one_tmul (x : A)
    (hx : IsIntegral S ((1 : S) ⊗ₜ[R] x)) : IsIntegral R x := by
  let E := Algebra.adjoin R ({x} : Set A)
  let xE : E := ⟨x, Algebra.subset_adjoin rfl⟩
  let f : S ⊗[R] E →ₐ[S] S ⊗[R] A :=
    Algebra.TensorProduct.map (AlgHom.id S S) E.val
  have hf : Function.Injective f :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  have hxval : E.val xE = x := rfl
  have hxE : IsIntegral S ((1 : S) ⊗ₜ[R] xE) := by
    apply (isIntegral_algHom_iff f hf).mp
    simpa only [f, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hxval] using hx
  have hset : ((↑) : E → A) ⁻¹' ({x} : Set A) = ({xE} : Set E) := by
    ext z
    change (z : A) = x ↔ z = xE
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hE : Algebra.adjoin R ({xE} : Set E) = ⊤ := by
    rw [← hset]
    exact Algebra.adjoin_adjoin_coe_preimage (R := R) (s := ({x} : Set A))
  have hT : Algebra.adjoin S ({(1 : S) ⊗ₜ[R] xE} : Set (S ⊗[R] E)) = ⊤ := by
    simpa only [Set.image_singleton] using
      (Algebra.TensorProduct.adjoin_one_tmul_image_eq_top
        (A := S) ({xE} : Set E) hE)
  let : Module.Finite S (Algebra.adjoin S ({(1 : S) ⊗ₜ[R] xE} : Set (S ⊗[R] E))) :=
    Algebra.finite_adjoin_simple_of_isIntegral hxE
  let e : Algebra.adjoin S ({(1 : S) ⊗ₜ[R] xE} : Set (S ⊗[R] E)) ≃ₐ[S]
      S ⊗[R] E :=
    (Subalgebra.equivOfEq _ _ hT).trans Subalgebra.topEquiv
  let : Module.Finite S (S ⊗[R] E) := Module.Finite.equiv e.toLinearEquiv
  let : Module.Finite R E := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  have hxR : IsIntegral R xE := _root_.IsIntegral.of_finite (R := R) (B := E) xE
  simpa only [hxval] using hxR.map E.val

end IntegralDescent

end Algebra.Descent.FormalGluing

namespace integralClosure

open Algebra.Descent.FormalGluing

variable (R : Type u) (S : Type v) (K : Type w) (Q : Type z)
  [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [Algebra R S] [Module.FaithfullyFlat R S]
  [CommRing K] [Algebra R K] [IsFractionRing R K]
  [CommRing Q] [Algebra S Q] [IsFractionRing S Q]

/-- A finitely generated supported conductor makes the original normalization
base-change map surjective. The quotient equivalence must agree with the
original coefficient map. The conductor condition is an equation in the actual
upper normalization, with its original scalar inclusion. -/
theorem flatBaseChangeHom_surjective_of_conductor
    (J : Ideal R) (hJ : J.FG) (t : R) (ht : t ∈ J) (ht0 : t ≠ 0)
    (e : R ⧸ J ≃+* S ⧸ J.map (algebraMap R S))
    (he : ∀ r : R, e (Ideal.Quotient.mk J r) =
      Ideal.Quotient.mk (J.map (algebraMap R S)) (algebraMap R S r))
    (hcond : ∀ s ∈ J.map (algebraMap R S), ∀ b : integralClosure S Q,
      ∃ a : S, algebraMap S (integralClosure S Q) a = s • b) :
    Function.Surjective (flatBaseChangeHom R S K Q) := by
  classical
  let B := integralClosure S Q
  let : IsDomain Q := IsFractionRing.isDomain S
  let : Algebra R B := ((algebraMap S B).comp (algebraMap R S)).toAlgebra
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  have hinj : Function.Injective (algebraMap S B) := by
    intro a b hab
    apply IsFractionRing.injective S Q
    exact congrArg (fun z : B => (z : Q)) hab
  obtain ⟨n, d, hd, hspan⟩ := exists_conductorFamily J hJ t ht
  subst t
  have hcd (i : Option (Fin n)) (b : B) :
      ∃ a : S, algebraMap S B a = algebraMap R S (d i) • b := by
    apply hcond
    apply Ideal.mem_map_of_mem
    rw [← hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hreg : IsSMulRegular R (d none) := by
    intro a b hab
    exact mul_left_cancel₀ ht0 hab
  have htB : algebraMap S B (algebraMap R S (d none)) ≠ 0 := by
    intro h
    apply ht0
    apply FaithfulSMul.algebraMap_injective R S
    apply hinj
    simpa only [map_zero] using h
  have hregB : IsSMulRegular B (algebraMap R S (d none)) := by
    intro a b hab
    apply mul_left_cancel₀ htB
    simpa only [Algebra.smul_def] using hab
  have hcoeff : Function.Surjective ((Ideal.Quotient.mk
      ((Ideal.span (Set.range d)).map (algebraMap R S))).comp (algebraMap R S)) := by
    rw [hspan]
    exact quotient_coefficients_surjective J e he
  let E := regularConductorSubalgebra (d none) hinj (hcd none)
  let ψ : E →ₐ[R] B := regularConductorMap (d none) hinj (hcd none) hregB
  have htK : IsUnit (algebraMap R K (d none)) :=
    IsLocalization.map_units K ⟨d none, mem_nonZeroDivisors_iff_ne_zero.mpr ht0⟩
  let l : Localization.Away (d none) →ₐ[R] K :=
    IsLocalization.Away.liftAlgHom (f := Algebra.ofId R K) (d none) htK
  let j : E →ₐ[R] K := l.comp E.val
  let F : S ⊗[R] K →ₐ[S] Q := flatFractionTensorMap R S K Q
  let i : K →+* Q := F.toRingHom.comp
    (Algebra.TensorProduct.includeRight : K →ₐ[R] S ⊗[R] K).toRingHom
  have hi (r : R) : i (algebraMap R K r) =
      algebraMap S Q (algebraMap R S r) :=
    flatFractionTensorMap_one_tmul_algebraMap R S K Q r
  have htQ : algebraMap S Q (algebraMap R S (d none)) ≠ 0 := by
    intro h
    apply ht0
    apply FaithfulSMul.algebraMap_injective R S
    apply IsFractionRing.injective S Q
    simpa only [map_zero] using h
  have hvalue (z : E) : F ((1 : S) ⊗ₜ[R] j z) = (ψ z : Q) := by
    obtain ⟨r, hr⟩ := regularConductorSubalgebra_conductor d none hinj hcd hreg hregB
      (d none) (Ideal.subset_span ⟨none, rfl⟩) z
    have hj : algebraMap R K r = algebraMap R K (d none) * j z := by
      calc
        algebraMap R K r = j (algebraMap R E r) := (j.commutes r).symm
        _ = j (d none • z) := congrArg j hr
        _ = algebraMap R K (d none) * j z := by rw [map_smul, Algebra.smul_def]
    have hψ : algebraMap R B r = d none • ψ z := by
      rw [← ψ.commutes r, hr, map_smul]
    have hψQ := congrArg (fun b : B => (b : Q)) hψ
    change algebraMap S Q (algebraMap R S r) =
      algebraMap S Q (algebraMap R S (d none)) * (ψ z : Q) at hψQ
    have hij := congrArg i hj
    rw [map_mul, hi, hi] at hij
    change i (j z) = (ψ z : Q)
    exact mul_left_cancel₀ htQ (hij.symm.trans hψQ)
  have hjIntegral (z : E) : IsIntegral R (j z) := by
    apply isIntegral_of_one_tmul (S := S)
    apply (isIntegral_algHom_iff F (flatFractionTensorMap_injective R S K Q)).mp
    rw [hvalue]
    exact (ψ z).property
  let k : E →ₐ[R] integralClosure R K := j.codRestrict _ hjIntegral
  let T : S ⊗[R] E →ₐ[S] S ⊗[R] integralClosure R K :=
    Algebra.TensorProduct.map (AlgHom.id S S) k
  have hT (z : S ⊗[R] E) : flatBaseChangeHom R S K Q (T z) =
      regularConductorBaseChange (d none) hinj (hcd none) hregB z := by
    induction z using TensorProduct.inductionOn with
    | tmul s z =>
        change flatBaseChangeHom R S K Q
          (Algebra.TensorProduct.map (AlgHom.id S S) k (s ⊗ₜ[R] z)) = _
        rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, regularConductorBaseChange_tmul]
        apply Subtype.ext
        rw [flatBaseChangeHom_tmul]
        have hkz : ((k z : integralClosure R K) : K) = j z := rfl
        rw [hkz]
        have hright : ((s • regularConductorMap (d none) hinj (hcd none) hregB z : B) : Q) =
            algebraMap S Q s * (ψ z : Q) := by
          dsimp only [B, ψ]
          rw [Subalgebra.coe_smul, Algebra.smul_def]
        rw [hright]
        change F (s ⊗ₜ[R] j z) = algebraMap S Q s * (ψ z : Q)
        have hsmul : s ⊗ₜ[R] j z = s • ((1 : S) ⊗ₜ[R] j z) := by
          simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hsmul, map_smul, Algebra.smul_def, hvalue]
    | add z w hz hw =>
        simp only [map_add, hz, hw]
  intro b
  obtain ⟨z, hz⟩ :=
    (regularConductorBaseChange_bijective d none hinj hcd hreg hregB hcoeff).surjective b
  exact ⟨T z, (hT z).trans hz⟩

/-- The supported-conductor theorem proves bijectivity of the already defined
normalization map, retaining its original fraction-tensor implementation. -/
theorem flatBaseChangeHom_bijective_of_conductor
    (J : Ideal R) (hJ : J.FG) (t : R) (ht : t ∈ J) (ht0 : t ≠ 0)
    (e : R ⧸ J ≃+* S ⧸ J.map (algebraMap R S))
    (he : ∀ r : R, e (Ideal.Quotient.mk J r) =
      Ideal.Quotient.mk (J.map (algebraMap R S)) (algebraMap R S r))
    (hcond : ∀ s ∈ J.map (algebraMap R S), ∀ b : integralClosure S Q,
      ∃ a : S, algebraMap S (integralClosure S Q) a = s • b) :
    Function.Bijective (flatBaseChangeHom R S K Q) :=
  ⟨flatBaseChangeHom_injective R S K Q,
    flatBaseChangeHom_surjective_of_conductor R S K Q J hJ t ht ht0 e he hcond⟩

/-- The canonical normalization algebra equivalence under the actual supported
conductor and original finite-order coefficient comparison. -/
def flatBaseChangeEquivOfConductor
    (J : Ideal R) (hJ : J.FG) (t : R) (ht : t ∈ J) (ht0 : t ≠ 0)
    (e : R ⧸ J ≃+* S ⧸ J.map (algebraMap R S))
    (he : ∀ r : R, e (Ideal.Quotient.mk J r) =
      Ideal.Quotient.mk (J.map (algebraMap R S)) (algebraMap R S r))
    (hcond : ∀ s ∈ J.map (algebraMap R S), ∀ b : integralClosure S Q,
      ∃ a : S, algebraMap S (integralClosure S Q) a = s • b) :
    S ⊗[R] integralClosure R K ≃ₐ[S] integralClosure S Q :=
  AlgEquiv.ofBijective (flatBaseChangeHom R S K Q)
    (flatBaseChangeHom_bijective_of_conductor R S K Q J hJ t ht ht0 e he hcond)

/-- The equivalence has exactly the original ambient value on each pure tensor. -/
@[simp]
theorem flatBaseChangeEquivOfConductor_tmul
    (J : Ideal R) (hJ : J.FG) (t : R) (ht : t ∈ J) (ht0 : t ≠ 0)
    (e : R ⧸ J ≃+* S ⧸ J.map (algebraMap R S))
    (he : ∀ r : R, e (Ideal.Quotient.mk J r) =
      Ideal.Quotient.mk (J.map (algebraMap R S)) (algebraMap R S r))
    (hcond : ∀ s ∈ J.map (algebraMap R S), ∀ b : integralClosure S Q,
      ∃ a : S, algebraMap S (integralClosure S Q) a = s • b)
    (s : S) (x : integralClosure R K) :
    (flatBaseChangeEquivOfConductor R S K Q J hJ t ht ht0 e he hcond (s ⊗ₜ[R] x) : Q) =
      flatFractionTensorMap R S K Q (s ⊗ₜ[R] (x : K)) := rfl

/-- Once the canonical comparison is an isomorphism, finiteness descends
without a Noetherian hypothesis on either coefficient ring. -/
theorem finite_of_conductor_of_finite_upper
    [Module.Finite S (integralClosure S Q)]
    (J : Ideal R) (hJ : J.FG) (t : R) (ht : t ∈ J) (ht0 : t ≠ 0)
    (e : R ⧸ J ≃+* S ⧸ J.map (algebraMap R S))
    (he : ∀ r : R, e (Ideal.Quotient.mk J r) =
      Ideal.Quotient.mk (J.map (algebraMap R S)) (algebraMap R S r))
    (hcond : ∀ s ∈ J.map (algebraMap R S), ∀ b : integralClosure S Q,
      ∃ a : S, algebraMap S (integralClosure S Q) a = s • b) :
    Module.Finite R (integralClosure R K) := by
  let θ := flatBaseChangeEquivOfConductor R S K Q J hJ t ht ht0 e he hcond
  let : Module.Finite S (S ⊗[R] integralClosure R K) :=
    Module.Finite.equiv θ.symm.toLinearEquiv
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S

end integralClosure
