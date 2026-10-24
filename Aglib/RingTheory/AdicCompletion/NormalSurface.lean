/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.SurfaceFormalFiber
public import Aglib.RingTheory.AdicCompletion.AssociatedPrimeCriterion
public import Aglib.RingTheory.Nagata.Completion
public import Aglib.RingTheory.LocalRing.ParameterIdeal
public import Aglib.RingTheory.RegularLocalRing.FiniteNormalAlgebra
public import Aglib.RingTheory.RegularLocalRing.Normal
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Regular.Flat

/-!
# Normal completions of actual surface charts

The original local surface is normal and Nagata and is supplied with an
injective local map from a complete local surface with finite residue
extension. Quotient completions, the zero-dimensional formal-fibre theorem,
and the regular parameter pair give normality of the same actual completion.
No G-ring, excellence, or normal-ascent conclusion is an input.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct nonZeroDivisors Pointwise

universe u

namespace AdicCompletion

private theorem not_associated_maximal_of_regular_pair
    (C : Type u) [CommRing C] [IsNoetherianRing C] [IsLocalRing C]
    (x y : C) (hx : IsSMulRegular C x)
    (hy : IsSMulRegular (C ⧸ Ideal.span {x}) y)
    (hxm : x ∈ maximalIdeal C) (hym : y ∈ maximalIdeal C)
    (b : C) (hb : b ∈ nonZeroDivisors C) :
    ¬ IsAssociatedPrime (maximalIdeal C) (C ⧸ Ideal.span {b}) := by
  intro h
  obtain ⟨_, c, hc⟩ := isAssociatedPrime_iff.mp h
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  have ha : Ideal.Quotient.mk (Ideal.span {b}) a ≠ 0 := by
    intro hz
    apply (maximalIdeal.isMaximal C).ne_top
    simpa only [hz, Submodule.colon_singleton_zero] using hc
  have hdiv (t : C) (ht : t ∈ maximalIdeal C) : b ∣ t * a := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have ht' : t ∈ (⊥ : Submodule C (C ⧸ Ideal.span {b})).colon
        {Ideal.Quotient.mk (Ideal.span {b}) a} := hc ▸ ht
    have hz := Submodule.mem_colon_singleton.mp ht'
    simpa only [Submodule.mem_bot, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      ← map_mul] using hz
  obtain ⟨v, hv⟩ := hdiv x hxm
  obtain ⟨w, hw⟩ := hdiv y hym
  have hregb : IsSMulRegular C b :=
    IsSMulRegular.of_right_eq_zero_of_smul fun t ht =>
      (mem_nonZeroDivisors_iff_left.mp hb) t ht
  have hyvxw : y * v = x * w := by
    apply hregb
    change b * (y * v) = b * (x * w)
    calc
      _ = y * (b * v) := by ring
      _ = y * (x * a) := by rw [← hv]
      _ = x * (y * a) := by ring
      _ = x * (b * w) := by rw [hw]
      _ = b * (x * w) := by ring
  have hvx : v ∈ Ideal.span {x} := by
    apply (isSMulRegular_quotient_iff_mem_of_smul_mem (Ideal.span {x}) y).mp hy v
    change y * v ∈ Ideal.span {x}
    rw [hyvxw]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_right x w)
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hvx
  have had : a = b * d := by
    apply hx
    change x * a = x * (b * d)
    rw [hv, hd]
    ring
  exact ha (Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton.mpr ⟨d, had⟩))

private def totalFractionToLocalFraction
    (C : Type u) [CommRing C] (P : Ideal C) [P.IsPrime] :
    FractionRing C →ₐ[C] FractionRing (Localization.AtPrime P) := by
  let Cp := Localization.AtPrime P
  let F := FractionRing Cp
  apply IsLocalization.liftAlgHom (M := nonZeroDivisors C) (f := Algebra.ofId C F)
  intro s
  have hs : algebraMap C Cp (s : C) ∈ nonZeroDivisors Cp :=
    IsLocalization.nonZeroDivisors_le_comap P.primeCompl Cp s.property
  change IsUnit (algebraMap C F (s : C))
  rw [IsScalarTower.algebraMap_apply C Cp F]
  exact IsLocalization.map_units F ⟨algebraMap C Cp (s : C), hs⟩

private theorem local_denominator_of_integral_fraction
    (C : Type u) [CommRing C] (P : Ideal C) [P.IsPrime]
    [IsIntegrallyClosed (Localization.AtPrime P)]
    (z : FractionRing C) (hz : IsIntegral C z) (a b : C)
    (hab : z * algebraMap C (FractionRing C) b = algebraMap C (FractionRing C) a) :
    ∃ s ∉ P, b ∣ s * a := by
  let Cp := Localization.AtPrime P
  let F := FractionRing Cp
  let ψ := totalFractionToLocalFraction C P
  have hz' : IsIntegral Cp (ψ z) := (hz.map ψ).tower_top
  obtain ⟨w, hw⟩ := (isIntegrallyClosed_iff F).mp
    (inferInstance : IsIntegrallyClosed Cp) hz'
  have hwb : w * algebraMap C Cp b = algebraMap C Cp a := by
    apply IsFractionRing.injective Cp F
    rw [map_mul, hw, ← IsScalarTower.algebraMap_apply C Cp F b,
      ← IsScalarTower.algebraMap_apply C Cp F a]
    rw [← ψ.commutes b, ← ψ.commutes a, ← map_mul, hab]
  obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.surj P.primeCompl w
  have hsab : algebraMap C Cp ((s : C) * a) = algebraMap C Cp (b * c) := by
    simp only [map_mul]
    calc
      _ = algebraMap C Cp (s : C) * (w * algebraMap C Cp b) := by rw [hwb]
      _ = algebraMap C Cp b * (w * algebraMap C Cp (s : C)) := by ring
      _ = algebraMap C Cp b * algebraMap C Cp c := by rw [hcs]
  obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists P.primeCompl Cp).mp hsab
  refine ⟨(t : C) * (s : C), ?_, ⟨(t : C) * c, ?_⟩⟩
  · exact fun h => ((inferInstance : P.IsPrime).mem_or_mem h).elim t.property s.property
  · calc
      _ = (t : C) * ((s : C) * a) := by ring
      _ = (t : C) * (b * c) := ht
      _ = b * ((t : C) * c) := by ring

/-- A regular pair and regular punctured spectrum give integral closedness
in the original total quotient ring. The source need not be a domain. -/
theorem isIntegrallyClosed_of_regular_pair_of_regular_nonmaximal
    (C : Type u) [CommRing C] [IsNoetherianRing C] [IsLocalRing C]
    (x y : C) (hx : IsSMulRegular C x)
    (hy : IsSMulRegular (C ⧸ Ideal.span {x}) y)
    (hxm : x ∈ maximalIdeal C) (hym : y ∈ maximalIdeal C)
    (hloc : ∀ (P : Ideal C) [P.IsPrime], P ≠ maximalIdeal C →
      IsRegularLocalRing (Localization.AtPrime P)) : IsIntegrallyClosed C := by
  apply (isIntegrallyClosed_iff (FractionRing C)).mpr
  intro z hz
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors C) z
  have hdiv : (b : C) ∣ a := by
    by_contra hdiv
    have ha : Ideal.Quotient.mk (Ideal.span {(b : C)}) a ≠ 0 := by
      simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using hdiv
    obtain ⟨P, hP, hann⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing C
      (Ideal.Quotient.mk (Ideal.span {(b : C)}) a) ha
    let : P.IsPrime := hP.isPrime
    have hPm : P ≠ maximalIdeal C := by
      intro he
      exact not_associated_maximal_of_regular_pair C x y hx hy hxm hym b b.property
        (he ▸ hP)
    let : IsRegularLocalRing (Localization.AtPrime P) := hloc P hPm
    let : IsDomain (Localization.AtPrime P) :=
      IsRegularLocalRing.isDomain_of_regularLocal _
    let : IsIntegrallyClosed (Localization.AtPrime P) :=
      IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _
    obtain ⟨s, hs, hsa⟩ := local_denominator_of_integral_fraction C P z hz a b hab
    apply hs
    apply hann
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    change Ideal.Quotient.mk (Ideal.span {(b : C)}) (s * a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hsa)
  obtain ⟨c, hc⟩ := hdiv
  refine ⟨c, ?_⟩
  apply (IsLocalization.map_units (FractionRing C) b).mul_right_cancel
  rw [hab, ← map_mul, mul_comm c, ← hc]

/-- Quotienting the actual completion by an original prime gives a reduced
ring, using Nagata on the original quotient and the native completion comparison. -/
theorem isReduced_primeQuotient_of_nagata_surface
    (B : Type u) [CommRing B] [IsLocalRing B]
    (hB : IsNagataRing.{u, 0} B) (hd : ringKrullDim B ≤ 2)
    (p : Ideal B) [p.IsPrime] :
    IsReduced ((AdicCompletion (maximalIdeal B) B) ⧸
      p.map (algebraMap B (AdicCompletion (maximalIdeal B) B))) := by
  let : IsNoetherianRing B := hB.isNoetherianRing
  let : IsLocalRing (B ⧸ p) := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  let : IsReduced (AdicCompletion (maximalIdeal (B ⧸ p)) (B ⧸ p)) :=
    (hB.quotient p).isReduced_completion_of_dimLE_two ((ringKrullDim_quotient_le p).trans hd)
  let e := quotientEquivPrimeCompletion B p
  exact isReduced_of_injective e e.injective

/-- Every ordinary formal fibre of a Nagata local surface is reduced.
This conclusion uses actual quotient completions and localization; it is not
a finite-field-extension geometric-reducedness assertion. -/
theorem isReduced_formalFiber_of_nagata_surface
    (B : Type u) [CommRing B] [IsLocalRing B]
    (hB : IsNagataRing.{u, 0} B) (hd : ringKrullDim B ≤ 2)
    (p : Ideal B) [p.IsPrime] :
    IsReduced (p.Fiber (AdicCompletion (maximalIdeal B) B)) := by
  let C := AdicCompletion (maximalIdeal B) B
  let M := Algebra.algebraMapSubmonoid C p.primeCompl
  let L := Localization M
  let I := p.map (algebraMap B C)
  let J := I.map (algebraMap C L)
  let : IsReduced (C ⧸ I) := isReduced_primeQuotient_of_nagata_surface B hB hd p
  let : Algebra (C ⧸ I) (L ⧸ J) := inferInstance
  let : IsScalarTower C (C ⧸ I) (L ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsReduced (L ⧸ J) := isReduced_localizationPreserves
    (Algebra.algebraMapSubmonoid (C ⧸ I) M) (L ⧸ J) inferInstance
  let : Algebra C (p.Fiber C) := Algebra.TensorProduct.rightAlgebra
  let e := Ideal.Fiber.algEquivAux₁ (S := C) p
  exact isReduced_of_injective e e.injective

private theorem idempotent_eq_zero_or_one_of_local
    (C : Type u) [CommRing C] [IsLocalRing C] (e : C) (he : e * e = e) :
    e = 0 ∨ e = 1 := by
  rcases isUnit_or_isUnit_one_sub_self e with h | h
  · exact Or.inr (h.mul_left_cancel (by simpa only [mul_one] using he))
  · apply Or.inl
    apply h.mul_left_cancel
    simp only [sub_mul, one_mul, he, sub_self, mul_zero]

private theorem idempotent_isIntegral
    (C F : Type u) [CommRing C] [CommRing F] [Algebra C F]
    (e : F) (he : e * e = e) : IsIntegral C e := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X,
    Polynomial.monic_X_pow_sub (Polynomial.degree_X_le.trans_lt (by norm_num)), ?_⟩
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X,
    pow_two, he, sub_self]

private theorem isDomain_of_artinian_total_fraction_ring
    (C F : Type u) [CommRing C] [IsLocalRing C] [IsIntegrallyClosed C]
    [CommRing F] [Algebra C F] [IsFractionRing C F]
    [IsReduced F] [IsArtinianRing F] : IsDomain C := by
  classical
  let : Nontrivial F := ⟨⟨0, 1, fun h => zero_ne_one
    ((IsFractionRing.injective C F) (by simpa only [_root_.map_zero, map_one] using h))⟩⟩
  let E := IsArtinianRing.equivPi F
  have hsub : Subsingleton (MaximalSpectrum F) := by
    constructor
    intro i j
    by_contra hij
    let v : ∀ k : MaximalSpectrum F, F ⧸ k.asIdeal := fun k => if k = i then 1 else 0
    let e : F := E.symm v
    have he : e * e = e := by
      apply E.injective
      change E (E.symm v * E.symm v) = E (E.symm v)
      rw [map_mul, E.apply_symm_apply]
      funext k
      by_cases hk : k = i <;> simp [v, hk]
    obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff F).mp
      (inferInstance : IsIntegrallyClosed C) (idempotent_isIntegral C F e he)
    have hcIdem : c * c = c := by
      apply IsFractionRing.injective C F
      rw [map_mul, hc, he]
    rcases idempotent_eq_zero_or_one_of_local C c hcIdem with hc0 | hc1
    · have he0 : e = 0 := by rw [← hc, hc0, _root_.map_zero]
      have hv0 := congrFun (congrArg E he0) i
      simp [e, v] at hv0
    · have he1 : e = 1 := by rw [← hc, hc1, map_one]
      have hv1 := congrFun (congrArg E he1) j
      have hji : j ≠ i := Ne.symm hij
      simp [e, v, hji] at hv1
  let i : MaximalSpectrum F := Classical.choice inferInstance
  let : Unique (MaximalSpectrum F) := ⟨⟨i⟩, fun j => hsub.elim j i⟩
  let e : F ≃+* F ⧸ i.asIdeal := E.toRingEquiv.trans (RingEquiv.piUnique _)
  let : Field (F ⧸ i.asIdeal) := Ideal.Quotient.field _
  let : IsDomain F := Function.Injective.isDomain e e.injective
  exact Function.Injective.isDomain (algebraMap C F) (IsFractionRing.injective C F)

section Surface

variable (A B : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
  [IsAdicComplete (maximalIdeal A) A]
  [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B]
  [IsIntegrallyClosed B] [Algebra A B] [IsLocalHom (algebraMap A B)]
  [Module.Finite (ResidueField A) (ResidueField B)]

/-- The original completion is regular at every nonclosed point. -/
theorem isRegularLocalRing_atPrime_of_complete_normal_surface
    (hinj : Function.Injective (algebraMap A B))
    (hA : ringKrullDim A = 2) (hB : ringKrullDim B = 2)
    (hN : IsNagataRing.{u, 0} B)
    (P : Ideal (AdicCompletion (maximalIdeal B) B)) [P.IsPrime]
    (hPm : P ≠ maximalIdeal (AdicCompletion (maximalIdeal B) B)) :
    IsRegularLocalRing (Localization.AtPrime P) := by
  let C := AdicCompletion (maximalIdeal B) B
  let p := P.comap (algebraMap B C)
  let : IsNoetherianRing C := AdicCompletion.isNoetherianRing B (maximalIdeal B)
  let : IsReduced C := hN.isReduced_completion_of_dimLE_two hB.le
  have hdC : ringKrullDim C = 2 :=
    (AdicCompletion.ringKrullDim_maximalIdeal_eq B).trans hB
  by_cases hp0 : p = ⊥
  · have hheight := height_eq_zero_of_comap_eq_bot_of_complete_surface A B hinj hA hB P hp0
    let Cp := Localization.AtPrime P
    let : Ring.KrullDimLE 0 Cp := Ring.KrullDimLE.of_isLocalization P
      (Ideal.height_eq_zero_iff.mp hheight) Cp
    let : IsReduced Cp := isReduced_localizationPreserves P.primeCompl Cp inferInstance
    let : Field Cp := Ring.KrullDimLE.isField_of_isReduced.toField
    infer_instance
  have hPbound : P.height ≤ 1 := by
    obtain ⟨n, hn, he⟩ := exists_ringKrullDim_localization_lt 2 hdC
      (⟨P, inferInstance⟩ : PrimeSpectrum C) hPm
    have he' : P.height = (n : ℕ∞) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)] at he
      exact WithBot.coe_injective he
    rw [he']
    exact_mod_cast (show n ≤ 1 by omega)
  let : P.LiesOver p := ⟨rfl⟩
  have hpbound : p.height ≤ 1 := by
    have he := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
    have hpP : p.height ≤ P.height := by
      rw [he]
      exact le_add_of_nonneg_right (bot_le : (0 : ℕ∞) ≤ _)
    exact hpP.trans hPbound
  let Bp := Localization.AtPrime p
  let : IsIntegrallyClosed Bp :=
    isIntegrallyClosed_of_isLocalization Bp p.primeCompl p.primeCompl_le_nonZeroDivisors
  have hdimBp : ringKrullDim Bp ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p Bp]
    exact_mod_cast hpbound
  have hnf : ¬ IsField Bp := by
    intro hf
    have he : p.height = 0 := by
      have hz := ringKrullDim_eq_zero_of_isField hf
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p Bp] at hz
      exact WithBot.coe_injective hz
    exact hp0 (Ideal.height_eq_zero_iff_eq_bot.mp he)
  let : IsDiscreteValuationRing Bp :=
    IsDiscreteValuationRing.of_isIntegrallyClosed_of_dimLE_one Bp hdimBp hnf
  let I := p.map (algebraMap B C)
  let : IsReduced (C ⧸ I) := isReduced_primeQuotient_of_nagata_surface B hN hB.le p
  obtain ⟨b, hb, hb0⟩ := p.ne_bot_iff.mp hp0
  have hreg : IsSMulRegular B b := IsSMulRegular.of_right_eq_zero_of_smul
    fun x hx => (mul_eq_zero.mp (show b * x = 0 from hx)).resolve_left hb0
  have hregC : IsSMulRegular C (algebraMap B C b) := hreg.of_flat
  have hnd : algebraMap B C b ∈ nonZeroDivisors C :=
    mem_nonZeroDivisors_iff_left.mpr fun x hx => hregC.right_eq_zero_of_smul hx
  have hIone : 1 ≤ I.height :=
    (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors hnd).trans
      (Ideal.height_mono ((Ideal.span_singleton_le_iff_mem I).mpr (Ideal.mem_map_of_mem _ hb)))
  have hIle : I ≤ P := Ideal.map_le_iff_le_comap.mpr le_rfl
  have hmin : P ∈ I.minimalPrimes :=
    Ideal.mem_minimalPrimes_of_height_le hIle (hPbound.trans hIone)
  have hass : IsAssociatedPrime P (C ⧸ I) := by
    apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes C (C ⧸ I)
    simpa only [Ideal.annihilator_quotient] using hmin
  exact IsRegularLocalRing.atPrime_of_flat_of_dvr_of_reduced_quotient B C p P rfl hass

/-- The actual completion is integrally closed in its actual total quotient
ring. Domainhood is established separately, rather than inferred from the
meaning of `IsIntegrallyClosed`. -/
theorem isIntegrallyClosed_of_complete_normal_surface
    (hinj : Function.Injective (algebraMap A B))
    (hA : ringKrullDim A = 2) (hB : ringKrullDim B = 2)
    (hN : IsNagataRing.{u, 0} B) :
    IsIntegrallyClosed (AdicCompletion (maximalIdeal B) B) := by
  let C := AdicCompletion (maximalIdeal B) B
  let : IsNoetherianRing C := AdicCompletion.isNoetherianRing B (maximalIdeal B)
  let : Ring.KrullDimLE 2 B := Ring.krullDimLE_iff.mpr hB.le
  have hm : maximalIdeal B ≠ ⊥ := by
    intro he
    have hz := ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.mpr he)
    rw [hB] at hz
    norm_num at hz
  obtain ⟨x, hxm, hx0⟩ := (maximalIdeal B).ne_bot_iff.mp hm
  obtain ⟨y, hym, hparam⟩ := exists_parameter_pair_containing B x hx0 hxm
  have hlist : (Ideal.ofList [x, y]).radical = maximalIdeal B := by
    rw [Ideal.ofList_cons, Ideal.ofList_singleton]
    exact hparam
  have hpair := IsIntegrallyClosed.isRegular_pair_of_radical_eq_maximalIdeal
    x y hx0 (by rw [hB]) hlist
  have hpairC := hpair.toIsWeaklyRegular.of_flat (S := C)
  simp only [List.map_cons, List.map_nil] at hpairC
  have hxC : IsSMulRegular C (algebraMap B C x) :=
    (RingTheory.Sequence.isWeaklyRegular_cons_iff C (algebraMap B C x)
      [algebraMap B C y]).mp hpairC |>.1
  have hyC : IsSMulRegular (QuotSMulTop (algebraMap B C x) C)
      (algebraMap B C y) := by
    have htail := (RingTheory.Sequence.isWeaklyRegular_cons_iff C (algebraMap B C x)
      [algebraMap B C y]).mp hpairC |>.2
    exact (RingTheory.Sequence.isWeaklyRegular_cons_iff _ (algebraMap B C y) []).mp htail |>.1
  have hquot : algebraMap B C x • (⊤ : Submodule C C) = Ideal.span {algebraMap B C x} := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  let e : QuotSMulTop (algebraMap B C x) C ≃ₗ[C]
      C ⧸ Ideal.span {algebraMap B C x} := Submodule.quotEquivOfEq _ _ hquot
  have hyQ : IsSMulRegular (C ⧸ Ideal.span {algebraMap B C x}) (algebraMap B C y) :=
    (e.isSMulRegular_congr (algebraMap B C y)).mp hyC
  apply isIntegrallyClosed_of_regular_pair_of_regular_nonmaximal C
    (algebraMap B C x) (algebraMap B C y) hxC hyQ
  · exact map_maximalIdeal_le (algebraMap B C) (Ideal.mem_map_of_mem _ hxm)
  · exact map_maximalIdeal_le (algebraMap B C) (Ideal.mem_map_of_mem _ hym)
  · intro P hP hPm
    exact isRegularLocalRing_atPrime_of_complete_normal_surface A B hinj hA hB hN P hPm

/-- Both normal-domain properties hold on the same actual completion.
The domain proof uses the zero-dimensional generic fibre as an Artinian total
quotient ring and descends its idempotents through proved integral closedness. -/
theorem normalDomain_of_complete_normal_surface
    (hinj : Function.Injective (algebraMap A B))
    (hA : ringKrullDim A = 2) (hB : ringKrullDim B = 2)
    (hN : IsNagataRing.{u, 0} B) :
    IsDomain (AdicCompletion (maximalIdeal B) B) ∧
      IsIntegrallyClosed (AdicCompletion (maximalIdeal B) B) := by
  let C := AdicCompletion (maximalIdeal B) B
  let : IsNoetherianRing C := AdicCompletion.isNoetherianRing B (maximalIdeal B)
  let : IsReduced C := hN.isReduced_completion_of_dimLE_two hB.le
  let : IsIntegrallyClosed C := isIntegrallyClosed_of_complete_normal_surface A B hinj hA hB hN
  let p : Ideal B := ⊥
  let M := Algebra.algebraMapSubmonoid C p.primeCompl
  let F := Localization M
  let : IsNoetherianRing F := IsLocalization.isNoetherianRing M F inferInstance
  let : Algebra C (p.Fiber C) := Algebra.TensorProduct.rightAlgebra
  let e : p.Fiber C ≃ₐ[C] F := (Ideal.Fiber.algEquivAux₁ (S := C) p).trans
    ((Ideal.quotientEquivAlgOfEq C (by simp only [p, Ideal.map_bot])).trans
      (AlgEquiv.quotientBot C F))
  let : Ring.KrullDimLE 0 (p.Fiber C) :=
    formalFiber_krullDimLE_zero_of_complete_surface A B hinj hA hB p
  let : Ring.KrullDimLE 0 F := by
    apply Ring.krullDimLE_iff.mpr
    rw [← e.toRingEquiv.ringKrullDim]
    exact Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 0 (p.Fiber C))
  let : IsArtinianRing F := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  have hM : M ≤ nonZeroDivisors C := by
    rintro _ ⟨b, hb, rfl⟩
    have hb0 : b ≠ 0 := by
      intro hz
      have hb' : b ∉ p := (Ideal.mem_primeCompl_iff (P := p)).mp hb
      apply hb'
      rw [hz]
      exact p.zero_mem
    have hreg : IsSMulRegular B b := IsSMulRegular.of_right_eq_zero_of_smul
      fun x hx => (mul_eq_zero.mp (show b * x = 0 from hx)).resolve_left hb0
    have hregC : IsSMulRegular C (algebraMap B C b) := hreg.of_flat
    exact mem_nonZeroDivisors_iff_left.mpr fun x hx => hregC.right_eq_zero_of_smul hx
  let : IsFractionRing C F := IsLocalization.of_le (S := F) M (nonZeroDivisors C) hM
    (fun c hc => IsArtinianRing.isUnit_of_mem_nonZeroDivisors
      (IsLocalization.nonZeroDivisors_le_comap M F hc))
  exact ⟨isDomain_of_artinian_total_fraction_ring C F, inferInstance⟩

end Surface

end AdicCompletion
