/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Blowup.ArcTermination
public import Aglib.RingTheory.Localization.Away.SaturatedChartLift
public import Aglib.RingTheory.Localization.ResiduePoint

/-!
# The original marked saturated chart

The literal chart and selected prime localization retain the original exceptional
ideal and coefficient map. An actual rational chart point identifies the original
residue fields. At a singular dimension-two point with three displayed generators,
Nakayama forces the same exceptional element to remain minimal.
-/

open IsLocalRing

@[expose] public noncomputable section

universe u

namespace IsLocalRing

/-- In a singular dimension-two local ring, none of three displayed maximal-ideal
generators can lie in the squared maximal ideal. Nakayama removes that generator. -/
theorem first_not_mem_sq_of_span_triple_of_not_regular
    (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (t x y : B) (hgen : maximalIdeal B = Ideal.span ({t, x, y} : Set B))
    (hd : ringKrullDim B = 2) (hsing : ¬ IsRegularLocalRing B) :
    t ∉ maximalIdeal B ^ 2 := by
  intro ht
  let J : Ideal B := Ideal.span ({x, y} : Set B)
  have hle : maximalIdeal B ≤ J ⊔ maximalIdeal B ^ 2 := by
    rw [hgen]
    apply Ideal.span_le.mpr
    intro b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl | rfl
    · exact Submodule.mem_sup_right (by simpa only [hgen] using ht)
    · exact Submodule.mem_sup_left (Ideal.subset_span (by simp))
    · exact Submodule.mem_sup_left (Ideal.subset_span (by simp))
  have hmJ : maximalIdeal B ≤ J := Submodule.le_of_le_smul_of_le_jacobson_bot
    (IsNoetherian.noetherian (maximalIdeal B : Submodule B B))
    (I := maximalIdeal B) (maximalIdeal_le_jacobson (⊥ : Ideal B))
    (by simpa only [smul_eq_mul, pow_two] using hle)
  have hJm : J ≤ maximalIdeal B := by
    apply Ideal.span_le.mpr
    intro b hb
    rw [hgen]
    exact Ideal.subset_span (Set.mem_insert_of_mem t hb)
  have hm : maximalIdeal B = J := le_antisymm hmJ hJm
  have hbound : (maximalIdeal B).spanFinrank ≤ 2 := by
    rw [hm]
    apply (Submodule.spanFinrank_span_le_ncard_of_finite
      ((Set.finite_singleton y).insert x)).trans
    simpa only [Set.ncard_singleton] using Set.ncard_insert_le x ({y} : Set B)
  apply hsing
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le B
  rw [hd]
  exact_mod_cast hbound

/-- The actual generic double-line quotient forces its division coefficient to be a unit.
Total divisibility and cancellation suffice; no numerical valuation is chosen. -/
theorem isUnit_of_generic_double_line_relation
    (D : Type u) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    (t v a : D) (hgen : maximalIdeal D = Ideal.span ({t, v} : Set D))
    (hv : v ∉ Ideal.span {t}) (hrel : v ^ 2 = t * a) : IsUnit a := by
  have hv0 : v ≠ 0 := by
    intro h
    apply hv
    rw [h]
    exact Ideal.zero_mem _
  have hdiv : v ∣ t := (ValuationRing.dvd_total t v).resolve_left
    (fun h => hv (Ideal.mem_span_singleton.mpr h))
  obtain ⟨b, htb⟩ := hdiv
  have hm : maximalIdeal D = Ideal.span {v} := by
    rw [hgen, Ideal.span_insert]
    exact sup_eq_right.mpr ((Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.mem_span_singleton.mpr ⟨b, htb⟩))
  have hb : ¬ IsUnit b := by
    rintro ⟨w, rfl⟩
    apply hv
    apply Ideal.mem_span_singleton.mpr
    refine ⟨((w⁻¹ : Dˣ) : D), ?_⟩
    rw [htb]
    simp only [mul_assoc, Units.mul_inv, mul_one]
  have hbmem : b ∈ maximalIdeal D := hb
  rw [hm] at hbmem
  obtain ⟨c, hbc⟩ := Ideal.mem_span_singleton.mp hbmem
  have htc : t = v ^ 2 * c := by
    rw [htb, hbc, pow_two, mul_assoc]
  have hca : c * a = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hv0)
    calc
      v ^ 2 * (c * a) = (v ^ 2 * c) * a := (mul_assoc _ _ _).symm
      _ = t * a := by rw [← htc]
      _ = v ^ 2 := hrel.symm
      _ = v ^ 2 * 1 := (mul_one _).symm
  exact isUnit_iff_dvd_one.mpr ⟨c, by simpa only [mul_comm] using hca.symm⟩

/-- In the original transformed relation, the binary-cubic coefficient has nonzero
generic residue. A relation suffices; no ambient hypersurface presentation is assumed. -/
theorem isUnit_cubic_coefficient_of_generic_double_line
    (D : Type u) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    (t v H l r : D) (hgen : maximalIdeal D = Ideal.span ({t, v} : Set D))
    (hv : v ∉ Ideal.span {t})
    (hrel : v ^ 2 + t * H + t * v * l + t ^ 2 * r = 0) : IsUnit H := by
  let a := -(H + v * l + t * r)
  have heq : v ^ 2 = t * a := by
    have hs : v ^ 2 + t * (H + v * l + t * r) = 0 := by
      calc
        _ = v ^ 2 + t * H + t * v * l + t ^ 2 * r := by ring
        _ = 0 := hrel
    simpa only [a, mul_neg] using (add_eq_zero_iff_eq_neg.mp hs)
  have hau := isUnit_of_generic_double_line_relation D t v a hgen hv heq
  by_contra hH
  have hHm : H ∈ maximalIdeal D := hH
  have ht : t ∈ maximalIdeal D := by
    rw [hgen]
    exact Ideal.subset_span (by simp)
  have hv' : v ∈ maximalIdeal D := by
    rw [hgen]
    exact Ideal.subset_span (by simp)
  have ha : a ∈ maximalIdeal D :=
    (maximalIdeal D).neg_mem ((maximalIdeal D).add_mem
      ((maximalIdeal D).add_mem hHm ((maximalIdeal D).mul_mem_right l hv'))
      ((maximalIdeal D).mul_mem_right r ht))
  exact (show ¬ IsUnit a from ha) hau

end IsLocalRing

namespace Localization.Away

variable {A : Type u} [CommRing A]

/-- Noetherianity of the literal saturated chart follows from its finite fraction generators. -/
theorem saturatedChart_isNoetherian (I : Ideal A) (a : A) [IsNoetherianRing A] :
    IsNoetherianRing (saturatedChart A I a) := by
  obtain ⟨s, hs⟩ := I.fg_of_isNoetherianRing
  apply isNoetherianRing_of_fg
  apply Subalgebra.fg_def.mpr
  refine ⟨fraction a '' (s : Set A), s.finite_toSet.image _, ?_⟩
  rw [← saturatedChart_span_eq_adjoin_fractions, hs]

/-- The actual coefficient map into the selected local saturated chart. -/
def localizedChartMap (I : Ideal A) (a : A) (q : Ideal (saturatedChart A I a)) [q.IsPrime] :
    A →+* Localization.AtPrime q :=
  (algebraMap (saturatedChart A I a) (Localization.AtPrime q)).comp
    (algebraMap A (saturatedChart A I a))

/-- The original centre extends to the principal ideal of the same original exceptional element. -/
theorem localizedChartMap_center (I : Ideal A) (a : A) (ha : a ∈ I)
    (q : Ideal (saturatedChart A I a)) [q.IsPrime] :
    I.map (localizedChartMap I a q) = Ideal.span {localizedChartMap I a q a} := by
  rw [localizedChartMap, ← Ideal.map_map, map_center_eq_span I a ha,
    Ideal.map_span, Set.image_singleton]
  rfl

/-- An actual rational point of the chart makes the original coefficient map to its
actual prime localization local. The point is valued in the original residue field. -/
theorem localizedChartMap_isLocal_of_residue_point [IsLocalRing A]
    (I : Ideal A) (a : A) (φ : saturatedChart A I a →+* ResidueField A)
    (hφ : φ.comp (algebraMap A (saturatedChart A I a)) = residue A) :
    IsLocalHom (localizedChartMap I a (Localization.ResiduePoint.ideal φ)) := by
  let c := localizedChartMap I a (Localization.ResiduePoint.ideal φ)
  have hc : (Localization.ResiduePoint.point φ).comp c = residue A := by
    apply RingHom.ext
    intro x
    exact (Localization.ResiduePoint.point_algebraMap φ
      (algebraMap A (saturatedChart A I a) x)).trans (RingHom.congr_fun hφ x)
  let : IsLocalHom ((Localization.ResiduePoint.point φ).comp c) :=
    hc.symm ▸ inferInstanceAs (IsLocalHom (residue A))
  exact isLocalHom_of_comp c (Localization.ResiduePoint.point φ)

/-- The original local coefficient map induces an isomorphism of actual residue fields
at the specified rational chart point. No residue-field section is chosen. -/
theorem localizedChartMap_residue_bijective [IsLocalRing A]
    (I : Ideal A) (a : A) (φ : saturatedChart A I a →+* ResidueField A)
    (hφ : φ.comp (algebraMap A (saturatedChart A I a)) = residue A) :
    let _ := localizedChartMap_isLocal_of_residue_point I a φ hφ
    Function.Bijective (ResidueField.map (R := A) (S := Localization.ResiduePoint.Ring φ)
      (localizedChartMap I a (Localization.ResiduePoint.ideal φ))) := by
  let : IsLocalHom (localizedChartMap I a (Localization.ResiduePoint.ideal φ)) :=
    localizedChartMap_isLocal_of_residue_point I a φ hφ
  let c : A →+* Localization.ResiduePoint.Ring φ :=
    localizedChartMap I a (Localization.ResiduePoint.ideal φ)
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨x, hx⟩ := residue_surjective (R := A) z
    exact ⟨algebraMap A (saturatedChart A I a) x, (RingHom.congr_fun hφ x).trans hx⟩
  let e := Localization.ResiduePoint.residueEquiv φ hsurj
  have he : e.toRingHom.comp
      (ResidueField.map (R := A) (S := Localization.ResiduePoint.Ring φ) c) =
      RingHom.id (ResidueField A) := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    change e (residue (Localization.ResiduePoint.Ring φ) (c x)) = residue A x
    exact (Localization.ResiduePoint.residueEquiv_algebraMap φ hsurj
      (algebraMap A (saturatedChart A I a) x)).trans (RingHom.congr_fun hφ x)
  refine ⟨(ResidueField.map (R := A) (S := Localization.ResiduePoint.Ring φ) c).injective, ?_⟩
  intro z
  exact ⟨e z, e.injective (RingHom.congr_fun he (e z))⟩

/-- At the literal rational coordinate point on the exceptional chart, singularity
and dimension two force the original exceptional element to remain minimal. -/
theorem localizedChart_parameter_not_mem_sq
    [IsLocalRing A] [IsNoetherianRing A]
    (t s z : maximalIdeal A) (α : A)
    (q : Ideal (saturatedChart A (maximalIdeal A) (t : A))) [q.IsPrime]
    (hq : q = Ideal.span
      ({algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A),
        SaturatedChart.fractionElement (maximalIdeal A) t s -
          algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) α,
        SaturatedChart.fractionElement (maximalIdeal A) t z} :
          Set (saturatedChart A (maximalIdeal A) (t : A))))
    (hd : ringKrullDim (Localization.AtPrime q) = 2)
    (hsing : ¬ IsRegularLocalRing (Localization.AtPrime q)) :
    localizedChartMap (maximalIdeal A) (t : A) q (t : A) ∉
      maximalIdeal (Localization.AtPrime q) ^ 2 := by
  let C := saturatedChart A (maximalIdeal A) (t : A)
  let B := Localization.AtPrime q
  let : IsNoetherianRing C := saturatedChart_isNoetherian (maximalIdeal A) (t : A)
  let : IsNoetherianRing B := IsLocalization.isNoetherianRing q.primeCompl B inferInstance
  have hgen : maximalIdeal B = Ideal.span
      ({algebraMap C B (algebraMap A C (t : A)),
        algebraMap C B (SaturatedChart.fractionElement (maximalIdeal A) t s - algebraMap A C α),
        algebraMap C B (SaturatedChart.fractionElement (maximalIdeal A) t z)} : Set B) := by
    have hqmap := congrArg (Ideal.map (algebraMap C B)) hq
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq,
      Set.image_singleton] at hqmap
    exact (IsLocalization.AtPrime.map_eq_maximalIdeal q B).symm.trans hqmap
  exact IsLocalRing.first_not_mem_sq_of_span_triple_of_not_regular B _ _ _ hgen hd hsing

end Localization.Away
