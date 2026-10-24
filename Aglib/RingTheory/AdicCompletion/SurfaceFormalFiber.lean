/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.FiniteGeneration
public import Aglib.RingTheory.AdicCompletion.RegularLocalRing
public import Aglib.RingTheory.KrullDimension.LocalDrop
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.RingTheory.Finiteness.NilpotentKer
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Formal fibres of local surfaces over a complete surface

For the original injective local map from a complete two-dimensional
Noetherian local domain to a two-dimensional Noetherian local domain, a
finite residue extension forces every actual formal fibre to have dimension
zero. A nonminimal generic formal prime would produce a one-dimensional
quotient finite over the complete base. The proof does not assume that the
completion is a domain, reduced, normal, or excellent.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u

namespace AdicCompletion

private theorem finite_quotient_of_maximal_radical
    (A T : Type u) [CommRing A] [CommRing T] [Algebra A T]
    [IsLocalRing T] [IsNoetherianRing T]
    [Module.Finite A (ResidueField T)]
    (J : Ideal T) (hJ : J.radical = maximalIdeal T) :
    Module.Finite A (T ⧸ J) := by
  have hle : J ≤ maximalIdeal T := Ideal.le_radical.trans hJ.le
  let f : T ⧸ J →ₐ[A] ResidueField T := Ideal.Quotient.factorₐ A hle
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hle
  have hker : RingHom.ker f.toRingHom =
      (maximalIdeal T).map (Ideal.Quotient.mk J) := Ideal.Quotient.factor_ker hle
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJ.symm.le
    (maximalIdeal T).fg_of_isNoetherianRing
  have hnil : IsNilpotent (RingHom.ker f.toRingHom) := by
    refine ⟨n, ?_⟩
    rw [hker, ← Ideal.map_pow]
    exact Ideal.map_mk_eq_bot_of_le hn
  let : IsNoetherianRing (T ⧸ J) := isNoetherianRing_of_surjective T (T ⧸ J)
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hfg := (RingHom.ker f.toRingHom).fg_of_isNoetherianRing
  exact Module.finite_of_surjective_of_ker_le_nilradical f hf
    (hfg.isNilpotent_iff_le_nilradical.mp hnil) hfg

/-- Coefficient completeness, a maximal-primary extended ideal, and finite
residue degree imply finiteness for the same local algebra map. No finiteness
or completeness of the target is assumed. -/
theorem finite_of_complete_base_of_maximal_radical
    (A T : Type u) [CommRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [Algebra A T] [Module.Finite A (ResidueField T)]
    (h : ((maximalIdeal A).map (algebraMap A T)).radical = maximalIdeal T) :
    Module.Finite A T := by
  let J := (maximalIdeal A).map (algebraMap A T)
  let : Module.Finite A (T ⧸ J) := finite_quotient_of_maximal_radical A T J h
  let e : (T ⧸ (maximalIdeal A • ⊤ : Submodule A T)) ≃ₗ[A] T ⧸ J :=
    (Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map (maximalIdeal A))).trans
      (Submodule.Quotient.restrictScalarsEquiv A J)
  let : Module.Finite A (T ⧸ (maximalIdeal A • ⊤ : Submodule A T)) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  apply Module.finite_of_isPrecomplete_of_le_jacobson (maximalIdeal A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal T) bot_ne_top]
  exact Ideal.le_radical.trans h.le

private theorem radical_eq_maximal_of_nonzero_of_dimLE_one
    (T : Type u) [CommRing T] [IsDomain T] [IsLocalRing T]
    [Ring.KrullDimLE 1 T] (J : Ideal T) (hJ : J ≠ ⊥)
    (hle : J ≤ maximalIdeal T) : J.radical = maximalIdeal T := by
  apply le_antisymm
  · exact (maximalIdeal.isMaximal T).isPrime.radical_le_iff.mpr hle
  · rw [J.radical_eq_sInf]
    apply le_sInf
    intro P hP
    have hP0 : P ≠ ⊥ := fun h => hJ (le_bot_iff.mp (h ▸ hP.1))
    have hmax : P.IsMaximal := hP.2.isMaximal_of_ne_bot hP0
    exact (IsLocalRing.eq_maximalIdeal hmax).symm.le

private theorem dimLE_one_of_integral_injective
    (A T : Type u) [CommRing A] [IsDomain A]
    [CommRing T] [IsDomain T] [Ring.KrullDimLE 1 T]
    [Algebra A T] [Algebra.IsIntegral A T]
    (hinj : Function.Injective (algebraMap A T)) : Ring.KrullDimLE 1 A := by
  apply (Ring.krullDimLE_one_iff_of_isPrime_bot (R := A)).mpr
  intro p hp0 hp
  let : p.IsPrime := hp
  have hker : RingHom.ker (algebraMap A T) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hinj
  obtain ⟨P, hP, hPp⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := T) p
      (by rw [hker]; exact bot_le)
  let : P.IsPrime := hP
  have hP0 : P ≠ ⊥ := by
    intro h
    apply hp0
    rw [← hPp, h]
    exact hker
  let : P.IsMaximal := hP.isMaximal_of_ne_bot hP0
  simpa only [hPp] using
    (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) P)

private theorem quotient_dimLE_one_of_positive_height
    (C : Type u) [CommRing C] [Nontrivial C]
    (hd : ringKrullDim C ≤ 2) (P : Ideal C) [P.IsPrime] (hP : P.height ≠ 0) :
    Ring.KrullDimLE 1 (C ⧸ P) := by
  let p : PrimeSpectrum C := ⟨P, inferInstance⟩
  have hp : 1 ≤ Order.height p := by
    rw [← p.height_eq_orderHeight]
    exact Order.one_le_iff_ne_zero.mpr hP
  have hsum : ((Order.height p + Order.coheight p : ℕ∞) : WithBot ℕ∞) ≤
      ringKrullDim C := by
    rw [ringKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact WithBot.coe_le_coe.mpr (le_iSup (fun q : PrimeSpectrum C =>
      Order.height q + Order.coheight q) p)
  have hco : ((Order.coheight p : ℕ∞) : WithBot ℕ∞) + 1 ≤ 2 := by
    calc
      _ = ((1 + Order.coheight p : ℕ∞) : WithBot ℕ∞) := by
        simp only [WithBot.coe_add, WithBot.coe_one, add_comm]
      _ ≤ ((Order.height p + Order.coheight p : ℕ∞) : WithBot ℕ∞) :=
        WithBot.coe_le_coe.mpr (add_le_add hp le_rfl)
      _ ≤ 2 := hsum.trans hd
  have hco' : ((Order.coheight p : ℕ∞) : WithBot ℕ∞) ≤ 1 := by
    apply ENat.WithBot.add_le_add_one_right_iff.mp
    convert hco using 1; norm_num
  apply Ring.krullDimLE_iff.mpr
  rw [ringKrullDim_quotient]
  change Order.krullDim (Set.Ici p) ≤ 1
  rw [← Order.coheight_eq_krullDim_Ici]
  exact hco'

section Surface

variable (A B : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
  [IsAdicComplete (maximalIdeal A) A]
  [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]
  [Module.Finite (ResidueField A) (ResidueField B)]

omit [IsDomain A] [IsAdicComplete (maximalIdeal A) A] [IsDomain B] in
private theorem finite_residue_prime_quotient
    (P : Ideal (AdicCompletion (maximalIdeal B) B)) [P.IsPrime] :
    letI := IsLocalRing.of_surjective'
      (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
    Module.Finite A (ResidueField ((AdicCompletion (maximalIdeal B) B) ⧸ P)) := by
  let C := AdicCompletion (maximalIdeal B) B
  let T := C ⧸ P
  let : IsLocalRing T := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  let : IsLocalHom (algebraMap C T) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  let : IsLocalHom (algebraMap B T) := by
    rw [IsScalarTower.algebraMap_eq B C T]
    infer_instance
  let f : B →ₐ[A] T := IsScalarTower.toAlgHom A B T
  let : IsLocalHom f := ⟨fun b hb =>
    IsLocalHom.map_nonunit (f := algebraMap B T) b hb⟩
  let g : ResidueField B →ₐ[A] ResidueField T := ResidueField.mapAlgHom f
  have hg : Function.Surjective g := by
    intro t
    obtain ⟨x, rfl⟩ := residue_surjective (R := T) t
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, hb⟩ := (AdicCompletion.residueField_map_bijective B).surjective (residue C c)
    obtain ⟨b, rfl⟩ := residue_surjective (R := B) b
    refine ⟨residue B b, ?_⟩
    have he := congrArg (ResidueField.map (Ideal.Quotient.mk P)) hb
    simp only [ResidueField.map_residue] at he
    change residue T (algebraMap B T b) = _
    rw [IsScalarTower.algebraMap_apply B C T]
    exact he
  let : Module.Finite A (ResidueField A) :=
    Module.Finite.of_surjective (Algebra.linearMap A (ResidueField A)) residue_surjective
  let : Module.Finite A (ResidueField B) := Module.Finite.trans (ResidueField A) _
  exact Module.Finite.of_surjective g.toLinearMap hg

omit [IsDomain B] in
/-- A prime in the actual completion above the generic point is minimal.
The finite-quotient contradiction uses the original complete base map. -/
theorem height_eq_zero_of_comap_eq_bot_of_complete_surface
    (hinj : Function.Injective (algebraMap A B))
    (hA : ringKrullDim A = 2) (hB : ringKrullDim B = 2)
    (P : Ideal (AdicCompletion (maximalIdeal B) B)) [P.IsPrime]
    (hP : P.comap (algebraMap B (AdicCompletion (maximalIdeal B) B)) = ⊥) :
    P.height = 0 := by
  by_contra hheight
  let C := AdicCompletion (maximalIdeal B) B
  let T := C ⧸ P
  let : IsNoetherianRing C := AdicCompletion.isNoetherianRing B (maximalIdeal B)
  let : IsLocalRing T := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  let : IsLocalHom (algebraMap C T) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  let : IsNoetherianRing T := isNoetherianRing_of_surjective C T
    (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  let : Ring.KrullDimLE 1 T := quotient_dimLE_one_of_positive_height C
    ((AdicCompletion.ringKrullDim_maximalIdeal_eq B).trans hB).le P hheight
  let : IsLocalHom (algebraMap B T) := by
    rw [IsScalarTower.algebraMap_eq B C T]
    infer_instance
  let : IsLocalHom (algebraMap A T) := by
    rw [IsScalarTower.algebraMap_eq A B T]
    infer_instance
  have hinjBT : Function.Injective (algebraMap B T) := by
    apply (injective_iff_map_eq_zero (algebraMap B T)).mpr
    intro b hb
    have hbP : algebraMap B C b ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp hb
    change b ∈ P.comap (algebraMap B C) at hbP
    have hPC : P.comap (algebraMap B C) = ⊥ := hP
    rw [hPC] at hbP
    exact Ideal.mem_bot.mp hbP
  have hinjAT : Function.Injective (algebraMap A T) := by
    rw [IsScalarTower.algebraMap_eq A B T]
    exact hinjBT.comp hinj
  let J := (maximalIdeal A).map (algebraMap A T)
  have hmA : maximalIdeal A ≠ ⊥ := by
    intro hm
    have hz := ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.mpr hm)
    rw [hA] at hz
    norm_num at hz
  obtain ⟨a, ha, ha0⟩ := (maximalIdeal A).ne_bot_iff.mp hmA
  have hJ0 : J ≠ ⊥ := by
    intro hJ
    have hz : algebraMap A T a = 0 := by
      have hmem : algebraMap A T a ∈ J := Ideal.mem_map_of_mem _ ha
      simpa only [hJ, Ideal.mem_bot] using hmem
    exact ha0 (hinjAT (hz.trans (_root_.map_zero (algebraMap A T)).symm))
  have hrad : J.radical = maximalIdeal T :=
    radical_eq_maximal_of_nonzero_of_dimLE_one T J hJ0
      (map_maximalIdeal_le (algebraMap A T))
  let : Module.Finite A (ResidueField T) := finite_residue_prime_quotient A B P
  let : Module.Finite A T := finite_of_complete_base_of_maximal_radical A T hrad
  have hdimA := Ring.krullDimLE_iff.mp (dimLE_one_of_integral_injective A T hinjAT)
  rw [hA] at hdimA
  norm_num at hdimA

/-- Comparable primes in a formal fibre of the original completion are equal. -/
theorem eq_of_le_of_comap_eq_of_complete_surface
    (hinj : Function.Injective (algebraMap A B))
    (hA : ringKrullDim A = 2) (hB : ringKrullDim B = 2)
    (P Q : Ideal (AdicCompletion (maximalIdeal B) B)) [P.IsPrime] [Q.IsPrime]
    (hPQ : P ≤ Q)
    (hbase : P.comap (algebraMap B (AdicCompletion (maximalIdeal B) B)) =
      Q.comap (algebraMap B (AdicCompletion (maximalIdeal B) B))) : P = Q := by
  let C := AdicCompletion (maximalIdeal B) B
  let p := P.comap (algebraMap B C)
  let : IsNoetherianRing C := AdicCompletion.isNoetherianRing B (maximalIdeal B)
  have hdC : ringKrullDim C = 2 :=
    (AdicCompletion.ringKrullDim_maximalIdeal_eq B).trans hB
  by_cases hp0 : p = ⊥
  · have hQ0 : Q.comap (algebraMap B C) = ⊥ := hbase.symm.trans hp0
    have hQmin : Q ∈ minimalPrimes C := Ideal.height_eq_zero_iff.mp
      (height_eq_zero_of_comap_eq_bot_of_complete_surface A B hinj hA hB Q hQ0)
    exact le_antisymm hPQ (hQmin.2 ⟨inferInstance, bot_le⟩ hPQ)
  by_cases hpm : p = maximalIdeal B
  · have hPmax : maximalIdeal C ≤ P := by
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.map_le_iff_le_comap.mpr hpm.symm.le
    exact le_antisymm hPQ ((le_maximalIdeal_of_isPrime Q).trans hPmax)
  by_contra hne
  have hlt : P < Q := lt_of_le_of_ne hPQ hne
  have hQm : Q ≠ maximalIdeal C := by
    intro h
    apply hpm
    change P.comap (algebraMap B C) = maximalIdeal B
    rw [hbase, h, IsLocalRing.maximalIdeal_comap]
  have hQbound : Q.height ≤ 1 := by
    obtain ⟨n, hn, he⟩ := exists_ringKrullDim_localization_lt 2 hdC
      (⟨Q, inferInstance⟩ : PrimeSpectrum C) hQm
    have hne : Q.height = (n : ℕ∞) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q)] at he
      exact WithBot.coe_injective he
    rw [hne]
    exact_mod_cast (show n ≤ 1 by omega)
  obtain ⟨b, hb, hb0⟩ := p.ne_bot_iff.mp hp0
  have hreg : IsSMulRegular B b := IsSMulRegular.of_right_eq_zero_of_smul
    fun x hx => (mul_eq_zero.mp (show b * x = 0 from hx)).resolve_left hb0
  have hregC : IsSMulRegular C (algebraMap B C b) := hreg.of_flat
  have hnd : algebraMap B C b ∈ nonZeroDivisors C :=
    mem_nonZeroDivisors_iff_left.mpr fun x hx => hregC.right_eq_zero_of_smul hx
  have hPone : 1 ≤ P.height :=
    (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors hnd).trans
      (Ideal.height_mono ((Ideal.span_singleton_le_iff_mem P).mpr hb))
  have htwo : (2 : ℕ∞) ≤ Q.height := by
    calc
      2 = 1 + 1 := by norm_num
      _ ≤ P.height + 1 := add_le_add hPone le_rfl
      _ ≤ Q.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have := htwo.trans hQbound
  norm_num at this

/-- Every actual residue-field tensor fibre of the local surface completion
has dimension zero. The tensor order is Mathlib's native `Ideal.Fiber`. -/
theorem formalFiber_krullDimLE_zero_of_complete_surface
    (hinj : Function.Injective (algebraMap A B))
    (hA : ringKrullDim A = 2) (hB : ringKrullDim B = 2)
    (p : Ideal B) [p.IsPrime] :
    Ring.KrullDimLE 0 (p.Fiber (AdicCompletion (maximalIdeal B) B)) := by
  let C := AdicCompletion (maximalIdeal B) B
  let e := PrimeSpectrum.primesOverOrderIsoFiber B C p
  apply Ring.krullDimLE_iff.mpr
  change Order.krullDim (PrimeSpectrum (p.Fiber C)) ≤ 0
  rw [← Order.krullDim_eq_of_orderIso e]
  apply Order.krullDim_nonpos_iff_forall_isMax.mpr
  intro P Q hPQ
  have hP : P.val.IsPrime := P.property.1
  have hQ : Q.val.IsPrime := Q.property.1
  let : P.val.IsPrime := hP
  let : Q.val.IsPrime := hQ
  have hbase : P.val.comap (algebraMap B C) = Q.val.comap (algebraMap B C) :=
    P.property.2.over.symm.trans Q.property.2.over
  have heq := eq_of_le_of_comap_eq_of_complete_surface A B hinj hA hB P.val Q.val hPQ hbase
  exact (Subtype.ext heq).ge

end Surface

end AdicCompletion
