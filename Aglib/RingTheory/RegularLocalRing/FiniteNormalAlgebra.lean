/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.HeightOneDivisibility
public import Aglib.RingTheory.RegularLocalRing.FiniteProjectiveDimension
public import Aglib.RingTheory.RegularLocalRing.RegularSequence
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Finite normal algebras over regular local surfaces

A finite injective local map from a regular local ring of dimension two to
a normal Noetherian local domain of dimension two makes the target finite
free over the source. The original parameter pair stays regular: finite
locality makes its ideal primary to the target maximal ideal, and height-one
divisibility proves regularity of the second parameter modulo the first.
Two actual regular-quotient projective-dimension identities then prove
projectivity. No completeness, coefficient field or Cohen--Macaulay premise
is imposed.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory IsLocalRing RingTheory.Sequence
open scoped Pointwise

namespace IsLocalRing

/-- An integral local map has only the closed target point above the closed
source point, expressed by the radical of the original extended maximal ideal. -/
theorem radical_map_maximalIdeal_of_isIntegral
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    [IsLocalRing R] [IsLocalRing A] (f : R →+* A) [IsLocalHom f]
    (hf : f.IsIntegral) :
    ((maximalIdeal R).map f).radical = maximalIdeal A := by
  apply le_antisymm
  · have hm : (maximalIdeal A).IsPrime := inferInstance
    exact hm.radical_le_iff.mpr (map_maximalIdeal_le f)
  · rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    intro P hP
    let : P.IsPrime := hP.2
    have hcomap : P.comap f = maximalIdeal R :=
      le_antisymm (le_maximalIdeal_of_isPrime (P.comap f))
        (Ideal.map_le_iff_le_comap.mp hP.1)
    have hmax : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap f hf P (by
        rw [hcomap]
        infer_instance)
    exact le_of_eq (eq_maximalIdeal hmax).symm

end IsLocalRing

namespace IsIntegrallyClosed

variable {A : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
  [IsIntegrallyClosed A]

/-- The original second multiplication is regular modulo the first parameter
when the pair is contained in no height-one prime of a normal domain. -/
theorem isSMulRegular_quotient_of_pair_avoids_height_one
    (a b : A) (ha : a ≠ 0)
    (havoid : ∀ P : Ideal A, P.IsPrime → P.height = 1 → a ∈ P → b ∉ P) :
    IsSMulRegular (A ⧸ Ideal.span {a}) b := by
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem (Ideal.span {a}) b).mpr
  intro x hx
  apply Ideal.mem_span_singleton.mpr
  have hdiv : a ∣ b * x := by
    simpa only [smul_eq_mul, Ideal.mem_span_singleton] using hx
  apply dvd_of_forall_height_one ha
  intro P hP hheight
  by_cases haP : a ∈ P
  · exact ⟨b, havoid P hP hheight haP, hdiv⟩
  · exact ⟨a, haP, dvd_mul_right a x⟩

variable [IsLocalRing A]

/-- A parameter pair in a normal local domain of dimension at least two is
regular, on its original successive quotients. -/
theorem isRegular_pair_of_radical_eq_maximalIdeal
    (a b : A) (ha : a ≠ 0) (hdim : 2 ≤ ringKrullDim A)
    (hrad : (Ideal.ofList [a, b]).radical = maximalIdeal A) :
    IsRegular A [a, b] := by
  have hmem : ∀ x ∈ [a, b], x ∈ maximalIdeal A := by
    intro x hx
    rw [← hrad]
    exact Ideal.le_radical (Ideal.subset_span hx)
  have havoid : ∀ P : Ideal A, P.IsPrime → P.height = 1 → a ∈ P → b ∉ P := by
    intro P hP hheight haP hbP
    let : P.IsPrime := hP
    have hle : Ideal.ofList [a, b] ≤ P := by
      apply Ideal.span_le.mpr
      intro x hx
      change x ∈ [a, b] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact haP
      · rcases List.mem_singleton.mp hx with rfl
        exact hbP
    have hmle : maximalIdeal A ≤ P := by
      rw [← hrad]
      exact hP.radical_le_iff.mpr hle
    have he : maximalIdeal A = P :=
      le_antisymm hmle (le_maximalIdeal_of_isPrime P)
    have hd := hdim
    rw [← maximalIdeal_height_eq_ringKrullDim, he, hheight] at hd
    norm_num at hd
  have haReg : IsSMulRegular A a := by
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro x hx
    change a * x = 0 at hx
    exact (mul_eq_zero.mp hx).resolve_left ha
  have hbReg : IsSMulRegular (A ⧸ Ideal.span {a}) b :=
    isSMulRegular_quotient_of_pair_avoids_height_one a b ha havoid
  have hquot : a • (⊤ : Submodule A A) = Ideal.span {a} := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  let e : QuotSMulTop a A ≃ₗ[A] A ⧸ Ideal.span {a} :=
    Submodule.quotEquivOfEq _ _ hquot
  have hbQuot : IsSMulRegular (QuotSMulTop a A) b :=
    (e.isSMulRegular_congr b).mpr hbReg
  exact IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal A hmem
    (IsWeaklyRegular.cons haReg
      (IsWeaklyRegular.cons hbQuot (IsWeaklyRegular.nil A _)))

/-- A supplied source parameter pair stays regular on the original finite
normal local algebra, for the original restricted scalar action. -/
theorem isRegular_pair_of_finite_local_algebra
    {R : Type u} [CommRing R] [IsLocalRing R] [Algebra R A]
    [Module.Finite R A] [IsLocalHom (algebraMap R A)]
    (hinj : Function.Injective (algebraMap R A)) (hdim : 2 ≤ ringKrullDim A)
    (u v : R) (hu : u ≠ 0) (hspan : Ideal.ofList [u, v] = maximalIdeal R) :
    IsRegular A [u, v] := by
  have hint : (algebraMap R A).IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  have hrad :
      (Ideal.ofList [algebraMap R A u, algebraMap R A v]).radical = maximalIdeal A := by
    have h := radical_map_maximalIdeal_of_isIntegral (algebraMap R A) hint
    rw [← hspan, Ideal.map_ofList] at h
    simpa only [List.map_cons, List.map_nil] using h
  have ha : algebraMap R A u ≠ 0 := fun h => hu (hinj (by simpa using h))
  have hreg := isRegular_pair_of_radical_eq_maximalIdeal
    (algebraMap R A u) (algebraMap R A v) ha hdim hrad
  have hweak : IsWeaklyRegular A [u, v] :=
    (isWeaklyRegular_map_algebraMap_iff A A [u, v]).mp
      (by simpa only [List.map_cons, List.map_nil] using hreg.toIsWeaklyRegular)
  have hmem : ∀ x ∈ [u, v], x ∈ maximalIdeal R := by
    intro x hx
    rw [← hspan]
    exact Ideal.subset_span hx
  exact IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal A hmem hweak

end IsIntegrallyClosed

namespace IsRegularLocalRing

variable {R A : Type u} [CommRing R] [CommRing A] [IsRegularLocalRing R]
  [IsLocalRing A] [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Algebra R A] [Module.Finite R A] [IsLocalHom (algebraMap R A)]

/-- The actual finite normal algebra has projective dimension zero over its
regular local two-dimensional base. Both ring dimensions concern the original rings. -/
theorem projectiveDimension_le_zero_of_finite_normal_dimension_two
    (hR : ringKrullDim R = 2) (hA : ringKrullDim A = 2)
    (hinj : Function.Injective (algebraMap R A)) :
    projectiveDimension (ModuleCat.of R A) ≤ 0 := by
  obtain ⟨rs, hlen, hreg, hspan⟩ :=
    exists_regular_sequence_maximalIdeal R 2 (by simpa using hR)
  obtain ⟨u, v, rfl⟩ := List.length_eq_two.mp hlen
  have huReg : IsSMulRegular R u := ((isRegular_cons_iff R u [v]).mp hreg).1
  have hu : u ≠ 0 := by
    intro hzero
    have hone : (1 : R) = 0 := huReg (by simp [hzero])
    exact one_ne_zero hone
  have hregA := IsIntegrallyClosed.isRegular_pair_of_finite_local_algebra
    hinj (by simp [hA]) u v hu hspan
  obtain ⟨huA, hvA⟩ := (isRegular_cons_iff A u [v]).mp hregA
  have hvQuot : IsSMulRegular (QuotSMulTop u A) v :=
    ((isRegular_cons_iff (QuotSMulTop u A) v []).mp hvA).1
  have huMem : u ∈ maximalIdeal R := by
    rw [← hspan]
    exact Ideal.subset_span (by simp)
  have hvMem : v ∈ maximalIdeal R := by
    rw [← hspan]
    exact Ideal.subset_span (by simp)
  let M := ModuleCat.of R A
  let N := ModuleCat.of R (QuotSMulTop u A)
  have hq : projectiveDimension (ModuleCat.of R (QuotSMulTop v N)) ≤ (2 : ℕ) :=
    projectiveDimension_le_dimension 2 R (by simpa using hR) _
  rw [ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular N v hvQuot hvMem,
    ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular M u huA huMem] at hq
  have htwo : (1 : WithBot ℕ∞) + 1 = (2 : ℕ) := by
    simpa only [Nat.cast_one] using (Nat.cast_add (R := WithBot ℕ∞) 1 1).symm
  have hcancel : projectiveDimension M + (2 : ℕ) ≤ (0 : WithBot ℕ∞) + (2 : ℕ) := by
    simpa only [add_assoc, htwo, zero_add] using hq
  exact (ENat.WithBot.add_le_add_natCast_right_iff (c := 2)).mp hcancel

/-- Projectivity of the original finite normal algebra over its regular local
two-dimensional base, with no flatness or Cohen--Macaulay premise. -/
theorem projective_of_finite_normal_dimension_two
    (hR : ringKrullDim R = 2) (hA : ringKrullDim A = 2)
    (hinj : Function.Injective (algebraMap R A)) : Module.Projective R A := by
  let : HasProjectiveDimensionLE (ModuleCat.of R A) 0 :=
    (projectiveDimension_le_iff _ 0).mp
      (projectiveDimension_le_zero_of_finite_normal_dimension_two hR hA hinj)
  let : Projective (ModuleCat.of R A) :=
    (projective_iff_hasProjectiveDimensionLE_zero (ModuleCat.of R A)).mpr inferInstance
  exact (ModuleCat.of R A).projective_of_module_projective

/-- A finite normal local algebra of dimension two is free over its actual
regular local two-dimensional base when the algebra map is injective and local. -/
theorem free_of_finite_normal_dimension_two
    (hR : ringKrullDim R = 2) (hA : ringKrullDim A = 2)
    (hinj : Function.Injective (algebraMap R A)) : Module.Free R A := by
  let : Module.Projective R A := projective_of_finite_normal_dimension_two hR hA hinj
  exact Module.free_of_flat_of_isLocalRing

end IsRegularLocalRing

namespace RingHom

/-- The finite-free conclusion for a specified finite injective local ring map.
The module structure is the one induced by this same map. -/
theorem Finite.free_of_normal_dimension_two
    {R A : Type u} [CommRing R] [CommRing A] [IsRegularLocalRing R]
    [IsLocalRing A] [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A]
    (f : R →+* A) [IsLocalHom f] (hf : f.Finite) (hinj : Function.Injective f)
    (hR : ringKrullDim R = 2) (hA : ringKrullDim A = 2) :
    letI := f.toAlgebra
    Module.Free R A := by
  let := f.toAlgebra
  let : Module.Finite R A := hf
  exact IsRegularLocalRing.free_of_finite_normal_dimension_two hR hA hinj

end RingHom
