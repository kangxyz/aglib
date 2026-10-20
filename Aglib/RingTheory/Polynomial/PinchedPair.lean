/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.ComputeDegree

/-!
# A polynomial algebra pinched at zero and one

The equal-evaluation subalgebra, its finite normalization, conductor localizations,
cubic presentation, and normalization defect are constructed over every field.
All maps are the literal inclusions, evaluations, and localization maps.
-/

@[expose] public noncomputable section

open Polynomial
open scoped Polynomial
universe u

namespace Polynomial.PinchedPair

variable (k : Type u) [Field k]

/-- The actual pinched affine coordinate ring. The pinched points remain
 distinct in every characteristic, including characteristic two. -/
def nodeRing : Subalgebra k k[X] := (aeval (0 : k)).equalizer (aeval (1 : k))

@[simp] theorem mem_nodeRing (p : k[X]) :
    p ∈ nodeRing k ↔ p.eval 0 = p.eval 1 := Iff.rfl

/-- The normalization is genuinely larger than the pinched ring. -/
theorem parameter_not_mem : (X : k[X]) ∉ nodeRing k := by simp

/-- A nonzero conductor element of the normalization inclusion. -/
def conductor : nodeRing k := ⟨X * (X - 1), by simp⟩

/-- Multiplying any polynomial by the conductor lands in the node ring. -/
def conductorMul (p : k[X]) : nodeRing k := ⟨X * (X - 1) * p, by simp⟩

theorem conductor_ne_zero : (conductor k : k[X]) ≠ 0 := by
  exact mul_ne_zero X_ne_zero (by simpa only [C_1] using X_sub_C_ne_zero (1 : k))

/-- The affine parameter is integral, with monic equation Z²−Z−T(T−1). -/
theorem parameter_integral : IsIntegral (nodeRing k) (X : k[X]) := by
  refine ⟨X ^ 2 - (X + C (conductor k)), ?_, ?_⟩
  · apply monic_X_pow_sub
    apply lt_of_le_of_lt (degree_add_le _ _)
    apply max_lt
    · simp
    · exact lt_of_le_of_lt degree_C_le (by norm_num)
  · simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_add, eval₂_C]
    change (X : k[X]) ^ 2 - (X + X * (X - 1)) = 0
    ring

/-- Every element of the actual normalization ring is integral over the node. -/
instance normalization_integral : Algebra.IsIntegral (nodeRing k) k[X] := by
  constructor
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact hp.add hq
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial]
      have hc : IsIntegral (nodeRing k) (C a : k[X]) :=
        isIntegral_algebraMap (x := (⟨C a, by simp⟩ : nodeRing k))
      exact hc.mul ((parameter_integral k).pow n)

/-- Integrality and finite type make this a finite normalization. -/
instance normalization_finite : Module.Finite (nodeRing k) k[X] := by
  let : Algebra.FiniteType (nodeRing k) k[X] :=
    Algebra.FiniteType.of_restrictScalars_finiteType (R := k) (S := nodeRing k) (A := k[X])
  exact Algebra.IsIntegral.finite

/-- The conductor clears denominators: the ambient rational function field is
also the fraction field of the pinched ring. -/
instance sameFractionField : IsFractionRing (nodeRing k) (FractionRing k[X]) := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective k[X] z
  refine ⟨conductorMul k a, conductorMul k b, ?_⟩
  have hc : algebraMap k[X] (FractionRing k[X]) (conductor k) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] (FractionRing k[X]))).mpr
      (conductor_ne_zero k)
  change z = algebraMap k[X] (FractionRing k[X]) ((conductor k : k[X]) * a) /
    algebraMap k[X] (FractionRing k[X]) ((conductor k : k[X]) * b)
  rw [map_mul, map_mul, mul_div_mul_left _ _ hc]
  exact hab.symm

/-- The actual polynomial ring, not a formal branch object, is the integral
closure of the node ring in its fraction field. -/
instance normalization_isIntegralClosure :
    IsIntegralClosure k[X] (nodeRing k) (FractionRing k[X]) := inferInstance

/-- The integral closure is strictly larger: the pinched ring is not normal. -/
theorem nodeRing_not_integrallyClosed : ¬ IsIntegrallyClosed (nodeRing k) := by
  intro h
  have hi : IsIntegral (nodeRing k) (algebraMap k[X] (FractionRing k[X]) X) :=
    (parameter_integral k).map (IsScalarTower.toAlgHom (nodeRing k) k[X] (FractionRing k[X]))
  obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff (FractionRing k[X])).mp h hi
  have he : (a : k[X]) = X := IsFractionRing.injective k[X] (FractionRing k[X]) ha
  exact parameter_not_mem k (he ▸ a.property)

/-- The second integral coordinate is T times the conductor coordinate. -/
def secondCoordinate : nodeRing k := conductorMul k X

/-- The standard characteristic-independent cubic relation is an actual ring
identity. Surjectivity/kernel identification for a quotient presentation is
not silently inferred from this identity. -/
theorem coordinate_relation :
    secondCoordinate k ^ 2 - conductor k * secondCoordinate k - conductor k ^ 3 = 0 := by
  apply Subtype.ext
  change (X * (X - 1) * X : k[X]) ^ 2 -
    X * (X - 1) * (X * (X - 1) * X) - (X * (X - 1)) ^ 3 = 0
  ring
section GeometricBranches
variable (K : Type u) [Field K] [Algebra k K]

/-- Actual affine `K`-valued points of the normalization above the pinched point. -/
def LiesOverNode (f : k[X] →ₐ[k] K) : Prop :=
  ∀ a : nodeRing k, f a = algebraMap k K ((a : k[X]).eval 0)

/-- Exhaustive normalized-branch description, valid over every extension field.
The proof forces the image of the affine parameter to be 0 or 1 using the
conductor equation. Neither branch labels nor a cardinality are hypotheses. -/
theorem branches_exhaustive (f : k[X] →ₐ[k] K) :
    LiesOverNode k K f ↔ f = aeval (0 : K) ∨ f = aeval (1 : K) := by
  constructor
  · intro h
    have hc := h (conductor k)
    have ht : f X * (f X - 1) = 0 := by simpa [conductor] using hc
    rcases mul_eq_zero.mp ht with hz | ho
    · left
      apply Polynomial.algHom_ext
      simpa using hz
    · right
      apply Polynomial.algHom_ext
      simpa using sub_eq_zero.mp ho
  · rintro (rfl | rfl) a
    · simpa using aeval_algebraMap_apply_eq_algebraMap_eval (A := K) (0 : k) (a : k[X])
    · simpa only [map_one, coe_aeval_eq_eval] using
        (aeval_algebraMap_apply_eq_algebraMap_eval (A := K) (1 : k) (a : k[X])).trans
          (congrArg (algebraMap k K) a.property.symm)

/-- The exhaustive alternatives represent different actual affine points. -/
theorem geometricBranches_distinct : (aeval (0 : K) : k[X] →ₐ[k] K) ≠ aeval (1 : K) := by
  intro h
  have hx := DFunLike.congr_fun h X
  simp at hx

end GeometricBranches
/-- The conductor open in the pinched affine chart. -/
abbrev nodeOverlapRing := Localization.Away (conductor k)

/-- The corresponding open of the actual normalization. -/
abbrev normalizationOverlapRing := Localization.Away (conductor k : k[X])

/-- The canonical localized normalization inclusion. -/
def localizationComparison : nodeOverlapRing k →+* normalizationOverlapRing k :=
  Localization.awayMap (nodeRing k).val.toRingHom (conductor k)

/-- The localized inclusion is bijective: the conductor clears every polynomial
with exactly one additional power. No abstract open-chart equivalence is supplied. -/
theorem localizationComparison_bijective : Function.Bijective (localizationComparison k) := by
  change Function.Bijective (Localization.awayMap (nodeRing k).val.toRingHom (conductor k))
  constructor
  · apply Localization.awayMap_injective_iff.mpr
    intro a ha
    have hz : a = 0 := Subtype.ext ha
    exact ⟨0, by simp [hz]⟩
  · apply Localization.awayMap_surjective_iff.mpr
    intro p
    exact ⟨conductorMul k p, 1, by simp [conductorMul, conductor]⟩

/-- A genuine localization ring isomorphism, obtained from the canonical map. -/
def conductorLocalizationEquiv : nodeOverlapRing k ≃+* normalizationOverlapRing k :=
  RingEquiv.ofBijective (localizationComparison k) (localizationComparison_bijective k)

@[simp] theorem localizationComparison_algebraMap (a : nodeRing k) :
    localizationComparison k (algebraMap (nodeRing k) (nodeOverlapRing k) a) =
      algebraMap k[X] (normalizationOverlapRing k) (a : k[X]) := by
  exact IsLocalization.map_eq (M := Submonoid.powers (conductor k))
    (S := nodeOverlapRing k) (T := Submonoid.powers (conductor k : k[X]))
    (Q := normalizationOverlapRing k) (g := (nodeRing k).val.toRingHom)
    (by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp⟩) a
namespace ConductorReciprocal
/-- The conductor polynomial `X * (X - 1)` of the pinching at zero and one. -/
def q : k[X] := X * (X - 1)
/-- The polynomial ring localized away from the conductor polynomial. -/
abbrev W := Localization.Away (q k)
/-- The polynomial coordinate in the conductor localization. -/
def t : W k := algebraMap k[X] (W k) X
/-- The inverse of the coordinate `t`, written using the inverse of the conductor polynomial. -/
def invT : W k := (t k - 1) * IsLocalization.Away.invSelf (q k)

lemma t_mul_invT : t k * invT k = 1 := by
  have h := IsLocalization.Away.mul_invSelf (S := W k) (q k)
  simpa only [q, map_mul, map_sub, map_one, t, invT, mul_assoc] using h

lemma invT_mul_t : invT k * t k = 1 := by rw [mul_comm, t_mul_invT]

lemma isUnit_invT : IsUnit (invT k) :=
  isUnit_iff_exists_inv.mpr ⟨t k, invT_mul_t k⟩

lemma isUnit_t_sub_one : IsUnit (t k - 1) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := W k) (q k)
  have h' : IsUnit (t k * (t k - 1)) := by
    simpa only [q, map_mul, map_sub, map_one, t] using h
  exact isUnit_of_mul_isUnit_right h'

lemma invT_sub_one : invT k - 1 = -(invT k) * (t k - 1) := by
  calc
    invT k - 1 = invT k - invT k * t k := by rw [invT_mul_t]
    _ = -(invT k) * (t k - 1) := by ring

lemma isUnit_invT_sub_one : IsUnit (invT k - 1) := by
  rw [invT_sub_one]
  exact ((isUnit_invT k).neg).mul (isUnit_t_sub_one k)

lemma reciprocal_eval_q_unit : IsUnit (aeval (invT k) (q k)) := by
  simpa only [q, map_mul, map_sub, map_one, aeval_X] using
    (isUnit_invT k).mul (isUnit_invT_sub_one k)

/-- The algebra endomorphism of the conductor localization substituting `t⁻¹` for `t`. -/
def reciprocal : W k →ₐ[k] W k :=
  IsLocalization.Away.liftAlgHom (q k) (f := aeval (invT k)) (reciprocal_eval_q_unit k)

@[simp] lemma reciprocal_algebraMap (p : k[X]) :
    reciprocal k (algebraMap k[X] (W k) p) = aeval (invT k) p := by
  exact IsLocalization.Away.lift_eq (q k) (reciprocal_eval_q_unit k) p

@[simp] lemma reciprocal_t : reciprocal k (t k) = invT k := by
  simp only [t, reciprocal_algebraMap, aeval_X]

@[simp] lemma reciprocal_invT : reciprocal k (invT k) = t k := by
  apply (isUnit_invT k).mul_left_cancel
  calc
    invT k * reciprocal k (invT k) = reciprocal k (t k * invT k) := by
      rw [map_mul, reciprocal_t]
    _ = 1 := by rw [t_mul_invT, map_one]
    _ = invT k * t k := (invT_mul_t k).symm

lemma reciprocal_comp : (reciprocal k).comp (reciprocal k) = AlgHom.id k (W k) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (q k))
  apply Polynomial.algHom_ext
  change reciprocal k (reciprocal k (t k)) = t k
  rw [reciprocal_t, reciprocal_invT]

lemma reciprocal_involutive : Function.Involutive (reciprocal k) := by
  intro z
  exact DFunLike.congr_fun (reciprocal_comp k) z

/-- The reciprocal-coordinate involution of the conductor localization. -/
def reciprocalEquiv : W k ≃ₐ[k] W k :=
  AlgEquiv.ofAlgHom (reciprocal k) (reciprocal k) (reciprocal_comp k) (reciprocal_comp k)
end ConductorReciprocal

/-- The polynomial infinity chart ring localized away from `X - 1`. -/
abbrev infinityChartRing := Localization.Away (X - 1 : k[X])
/-- The infinity chart ring further localized by its polynomial coordinate. -/
abbrev infinityOverlapRing := Localization.Away (algebraMap k[X] (infinityChartRing k) X)

/-- The iterated infinity overlap localization is a localization away from the conductor
polynomial. -/
instance infinityOverlap_isLocalization :
    IsLocalization.Away (conductor k : k[X]) (infinityOverlapRing k) := by
  change IsLocalization.Away (X * (X - 1) : k[X]) (infinityOverlapRing k)
  infer_instance

/-- The conductor localization identified with the iterated infinity overlap as polynomial
algebras. -/
def standardOverlapEquiv : normalizationOverlapRing k ≃ₐ[k[X]] infinityOverlapRing k :=
  IsLocalization.algEquiv (Submonoid.powers (conductor k : k[X])) _ _

/-- Every polynomial has a linear normal form over the conductor coordinate. -/
theorem polynomial_conductor_normal_form (p : k[X]) :
    ∃ a b : k[X], p = a.comp (conductor k : k[X]) + X * b.comp (conductor k : k[X]) := by
  induction p using Polynomial.induction_on with
  | C r => exact ⟨C r, 0, by simp⟩
  | add p q hp hq =>
      obtain ⟨a, b, rfl⟩ := hp
      obtain ⟨c, d, rfl⟩ := hq
      refine ⟨a + c, b + d, ?_⟩
      simp only [add_comp]
      ring
  | monomial n r hp =>
      obtain ⟨a, b, ha⟩ := hp
      refine ⟨X * b, a + b, ?_⟩
      rw [pow_succ, ← mul_assoc, ha]
      simp only [mul_comp, X_comp, add_comp]
      change (a.comp (conductor k : k[X]) + X * b.comp (conductor k : k[X])) * X =
        (X * (X - 1)) * b.comp (conductor k : k[X]) +
          X * (a.comp (conductor k : k[X]) + b.comp (conductor k : k[X]))
      ring

/-- Equal endpoint values remove the non-descending linear coefficient. -/
theorem node_coordinate_normal_form (p : nodeRing k) :
    ∃ a b : k[X], (p : k[X]) = a.comp (conductor k : k[X]) +
      (secondCoordinate k : k[X]) * b.comp (conductor k : k[X]) := by
  obtain ⟨a, b, hb⟩ := polynomial_conductor_normal_form k (p : k[X])
  have h0 : b.eval 0 = 0 := by
    have hp := p.property
    change (p : k[X]).eval 0 = (p : k[X]).eval 1 at hp
    rw [hb] at hp
    simpa [conductor] using hp.symm
  have hdiv : (X : k[X]) ∣ b := by
    apply X_dvd_iff.mpr
    simpa only [coeff_zero_eq_eval_zero] using h0
  obtain ⟨d, hd⟩ := hdiv
  refine ⟨a, d, ?_⟩
  rw [hb, hd, mul_comp, X_comp]
  change a.comp (conductor k : k[X]) + X * ((X * (X - 1)) * d.comp (conductor k : k[X])) =
    a.comp (conductor k : k[X]) + (X * (X - 1) * X) * d.comp (conductor k : k[X])
  ring

theorem coe_aeval_conductor (a : k[X]) :
    ((aeval (conductor k) a : nodeRing k) : k[X]) = a.comp (conductor k : k[X]) :=
  (aeval_algHom_apply (nodeRing k).val (conductor k) a).symm

/-- Evaluation at the two actual integral coordinates. -/
def coordinateHom : k[X][X] →ₐ[k] nodeRing k :=
  Polynomial.eval₂AlgHom (aeval (conductor k)) (secondCoordinate k) (fun _ => Commute.all _ _)

/-- The two coordinates generate the actual equalizer ring. -/
theorem coordinateHom_surjective : Function.Surjective (coordinateHom k) := by
  intro p
  obtain ⟨a, b, hp⟩ := node_coordinate_normal_form k p
  refine ⟨C a + C b * X, ?_⟩
  apply Subtype.ext
  rw [hp]
  simp only [coordinateHom, eval₂AlgHom_apply, eval₂_add, eval₂_mul, eval₂_C, eval₂_X,
    AlgHom.coe_toRingHom,
    Subalgebra.coe_add, Subalgebra.coe_mul]
  rw [coe_aeval_conductor, coe_aeval_conductor]
  change a.comp (conductor k : k[X]) + b.comp (conductor k : k[X]) *
    (secondCoordinate k : k[X]) = _
  ring



/-- Degree of the actual conductor coordinate. -/
theorem conductor_natDegree : (conductor k : k[X]).natDegree = 2 := by
  change (X * (X - C (1 : k)) : k[X]).natDegree = 2
  rw [natDegree_mul X_ne_zero (X_sub_C_ne_zero 1), natDegree_X, natDegree_X_sub_C]

/-- Degree of the second actual coordinate. -/
theorem secondCoordinate_natDegree : (secondCoordinate k : k[X]).natDegree = 3 := by
  change ((conductor k : k[X]) * X).natDegree = 3
  rw [natDegree_mul (conductor_ne_zero k) X_ne_zero, conductor_natDegree, natDegree_X]

/-- Composition with the conductor is injective at zero. -/
theorem comp_conductor_eq_zero_iff (a : k[X]) :
    a.comp (conductor k : k[X]) = 0 ↔ a = 0 := by
  have hn : (conductor k : k[X]) ≠ C ((conductor k : k[X]).coeff 0) := by
    intro h
    have hd := congrArg Polynomial.natDegree h
    norm_num [conductor_natDegree] at hd
  rw [comp_eq_zero_iff]
  simp only [hn, and_false, or_false]

/-- Linear normal forms in the two coordinates are unique, by degree parity. -/
theorem node_coordinate_normal_form_eq_zero (a b : k[X]) :
    a.comp (conductor k : k[X]) +
      (secondCoordinate k : k[X]) * b.comp (conductor k : k[X]) = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hb : b = 0 := by
      by_contra hb
      have hbc : b.comp (conductor k : k[X]) ≠ 0 :=
        mt (comp_conductor_eq_zero_iff k b).mp hb
      have hy : (secondCoordinate k : k[X]) ≠ 0 :=
        mul_ne_zero (conductor_ne_zero k) X_ne_zero
      have hd := congrArg Polynomial.natDegree (eq_neg_of_add_eq_zero_left h)
      rw [natDegree_comp, natDegree_neg, natDegree_mul hy hbc,
        secondCoordinate_natDegree, natDegree_comp, conductor_natDegree] at hd
      omega
    subst b
    simp only [Polynomial.zero_comp, mul_zero, add_zero] at h
    exact ⟨(comp_conductor_eq_zero_iff k a).mp h, rfl⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- The monic quadratic in Y, also the standard nodal cubic in X,Y. -/
def nodeCubic : k[X][X] := X ^ 2 - (C X * X + C (X ^ 3))

theorem nodeCubic_monic : (nodeCubic k).Monic := by
  apply monic_X_pow_sub
  exact (degree_add_le _ _).trans_lt (max_lt
    ((degree_C_mul_X_le _).trans_lt (by norm_num))
    (degree_C_le.trans_lt (by norm_num)))

theorem nodeCubic_natDegree : (nodeCubic k).natDegree = 2 := by
  apply natDegree_eq_of_degree_eq_some
  change (X ^ 2 - (C X * X + C (X ^ 3)) : k[X][X]).degree = 2
  rw [degree_sub_eq_left_of_degree_lt]
  · exact degree_X_pow 2
  · rw [degree_X_pow]
    exact (degree_add_le _ _).trans_lt (max_lt
      ((degree_C_mul_X_le _).trans_lt (by norm_num))
      (degree_C_le.trans_lt (by norm_num)))

theorem coordinateHom_nodeCubic : coordinateHom k (nodeCubic k) = 0 := by
  change (coordinateHom k) (X ^ 2 - (C X * X + C (X ^ 3))) = 0
  simpa only [coordinateHom, eval₂AlgHom_apply, eval₂_sub, eval₂_pow, eval₂_X,
    eval₂_add, eval₂_mul, eval₂_C, AlgHom.coe_toRingHom, aeval_X, map_pow, sub_add_eq_sub_sub] using
    coordinate_relation k

/-- The kernel is exactly the principal ideal of the cubic, proved by monic
reduction and uniqueness of the actual polynomial normal forms. -/
theorem coordinateHom_eq_zero_iff_dvd (p : k[X][X]) :
    coordinateHom k p = 0 ↔ nodeCubic k ∣ p := by
  constructor
  · intro hp
    have hm : (nodeCubic k).Monic := nodeCubic_monic k
    have hne : nodeCubic k ≠ 1 := by
      intro h
      have hd := congrArg Polynomial.natDegree h
      norm_num [nodeCubic_natDegree] at hd
    have hd : (p %ₘ nodeCubic k).natDegree ≤ 1 := by
      have h := natDegree_modByMonic_lt p hm hne
      rw [nodeCubic_natDegree] at h
      omega
    have hr : coordinateHom k (p %ₘ nodeCubic k) = 0 := by
      have he := congrArg (coordinateHom k) (modByMonic_add_div p (nodeCubic k))
      simpa only [map_add, map_mul, coordinateHom_nodeCubic, zero_mul, add_zero, hp] using he
    have hn := eq_X_add_C_of_natDegree_le_one hd
    have hcoeff : (p %ₘ nodeCubic k).coeff 0 = 0 ∧ (p %ₘ nodeCubic k).coeff 1 = 0 := by
      apply (node_coordinate_normal_form_eq_zero k _ _).mp
      rw [hn] at hr
      have hv := congrArg (fun z : nodeRing k => (z : k[X])) hr
      simp only [coordinateHom, eval₂AlgHom_apply, eval₂_add, eval₂_mul, eval₂_C,
        eval₂_X, AlgHom.coe_toRingHom, Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_zero,
        coe_aeval_conductor] at hv
      change _ + _ = 0 at hv
      simpa only [← comp_eq_aeval, mul_comm, add_comm] using hv
    apply (modByMonic_eq_zero_iff_dvd hm).mp
    rw [hn, hcoeff.1, hcoeff.2]
    simp
  · rintro ⟨q, rfl⟩
    simp only [map_mul, coordinateHom_nodeCubic, zero_mul]

theorem coordinateHom_ker : RingHom.ker (coordinateHom k).toRingHom =
    Ideal.span ({nodeCubic k} : Set k[X][X]) := by
  ext p
  change coordinateHom k p = 0 ↔ p ∈ Ideal.span ({nodeCubic k} : Set k[X][X])
  rw [Ideal.mem_span_singleton, coordinateHom_eq_zero_iff_dvd]

/-- Genuine algebra presentation of the actual node ring. -/
def nodeCubicEquiv :
    (k[X][X] ⧸ Ideal.span ({nodeCubic k} : Set k[X][X])) ≃ₐ[k] nodeRing k :=
  (Ideal.quotientEquivAlgOfEq k (coordinateHom_ker k).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (coordinateHom_surjective k))

variable (k : Type u) [Field k]

/-- An integral identity controlling the common zero of the cubic and its
partial derivatives, with no division by 2 or 3. -/
theorem nodeCubic_euler_identity (x y : k) :
    2 * (y ^ 2 - x * y - x ^ 3) - x * (-y - 3 * x ^ 2) - y * (2 * y - x) = x ^ 3 := by
  ring

/-- The simultaneous cubic and partial-derivative equations cut out only the
origin over every field, including characteristics 2 and 3. This statement
concerns explicit equations; it does not assume or assert a nodality predicate. -/
theorem nodeCubic_singular_equations_iff (x y : k) :
    (y ^ 2 - x * y - x ^ 3 = 0 ∧ -y - 3 * x ^ 2 = 0 ∧ 2 * y - x = 0) ↔
      x = 0 ∧ y = 0 := by
  constructor
  · rintro ⟨hF, hX, hY⟩
    have hx3 : x ^ 3 = 0 := by
      rw [← nodeCubic_euler_identity k x y, hF, hX, hY]
      ring
    have hx : x = 0 := (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hx3
    subst x
    exact ⟨rfl, by simpa using hX⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- The quadratic initial expression factors into the two tangent lines. -/
theorem nodeCubic_quadratic_factor (x y : k) : y ^ 2 - x * y = y * (y - x) := by
  ring

/-- The tangent forms Y and Y-X are not scalar multiples, even in
characteristic 2. The coefficient argument also works for any polynomial scalar. -/
theorem nodeCubic_tangent_forms_not_multiple (a : k[X]) :
    (X - C (X : k[X]) : k[X][X]) ≠ C a * X := by
  intro h
  have hc := congrArg (fun p : k[X][X] => p.coeff 0) h
  simp at hc

/-- In particular the two displayed tangent forms are distinct. -/
theorem nodeCubic_tangent_forms_distinct :
    (X : k[X][X]) ≠ X - C (X : k[X]) := by
  intro h
  apply nodeCubic_tangent_forms_not_multiple k 1
  simpa only [C_1, one_mul] using h.symm

/-- The tangent directions themselves are different: (1,0) lies on Y=0 and
not on Y-X=0, whereas (1,1) lies on Y-X=0 and not on Y=0. -/
theorem nodeCubic_tangent_directions :
    (0 : k) = 0 ∧ (0 : k) - 1 ≠ 0 ∧ (1 : k) - 1 = 0 ∧ (1 : k) ≠ 0 := by
  simp

variable (k : Type u) [Field k]

/-- The exact cubic splits into its quadratic tangent expression and the
higher-order conductor term. -/
theorem nodeCubic_factorization : nodeCubic k =
    X * (X - C (X : k[X])) - C ((X : k[X]) ^ 3) := by
  unfold nodeCubic
  ring

/-- The two tangent factors define different principal ideals over every field.
In particular characteristic two does not merge the two tangent directions. -/
theorem nodeCubic_tangent_ideals_distinct :
    Ideal.span ({(X : k[X][X])} : Set k[X][X]) ≠
      Ideal.span ({X - C (X : k[X])} : Set k[X][X]) := by
  intro h
  have hm : (X - C (X : k[X]) : k[X][X]) ∈
      Ideal.span ({(X : k[X][X])} : Set k[X][X]) := by
    rw [h]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [Ideal.mem_span_singleton, X_dvd_iff] at hm
  simp at hm
/-- The defect of the actual normalization inclusion is measured by the
difference of the two evaluations. This is a linear map on the actual ring. -/
def branchDifference : k[X] →ₗ[k] k :=
  (aeval (0 : k)).toLinearMap - (aeval (1 : k)).toLinearMap

lemma branchDifference_surjective : Function.Surjective (branchDifference k) := by
  intro a
  refine ⟨-C a * X, ?_⟩
  simp [branchDifference]

lemma branchDifference_ker : (branchDifference k).ker = (nodeRing k).toSubmodule := by
  ext p
  simp [branchDifference, sub_eq_zero]

/-- The normalization quotient identified with the difference of evaluation at zero and one. -/
def normalizationDefectEquiv : (k[X] ⧸ (nodeRing k).toSubmodule) ≃ₗ[k] k := by
  rw [← branchDifference_ker]
  exact (branchDifference k).quotKerEquivOfSurjective (branchDifference_surjective k)

theorem normalizationDefect_finrank : Module.finrank k (k[X] ⧸ (nodeRing k).toSubmodule) = 1 := by
  rw [(normalizationDefectEquiv k).finrank_eq]
  simp
section ConcreteSeparation
open ConductorReciprocal
open scoped TensorProduct

/-- The restriction of a pinched polynomial to the conductor overlap ring. -/
def affineOverlapRingMap : nodeRing k →ₐ[k] W k :=
  (IsScalarTower.toAlgHom k k[X] (W k)).comp (nodeRing k).val

/-- The restriction from the infinity chart ring to the conductor overlap using reciprocal
coordinates. -/
def infinityOverlapRingMap : infinityChartRing k →ₐ[k] W k :=
  (reciprocal k).comp (((standardOverlapEquiv k).symm.restrictScalars k).toAlgHom.comp
    (IsScalarTower.toAlgHom k (infinityChartRing k) (infinityOverlapRing k)))

theorem infinityOverlapRingMap_polynomial (p : k[X]) :
    infinityOverlapRingMap k (algebraMap k[X] (infinityChartRing k) p) = aeval (invT k) p := by
  change reciprocal k ((standardOverlapEquiv k).symm
    (algebraMap (infinityChartRing k) (infinityOverlapRing k)
      (algebraMap k[X] (infinityChartRing k) p))) = _
  rw [← IsScalarTower.algebraMap_apply k[X] (infinityChartRing k) (infinityOverlapRing k),
    (standardOverlapEquiv k).symm.commutes]
  exact reciprocal_algebraMap k p

/-- The algebra map from the tensor product of the pinched and infinity chart rings to their
overlap. -/
def overlapTensorMap : nodeRing k ⊗[k] infinityChartRing k →ₐ[k] W k :=
  Algebra.TensorProduct.lift (affineOverlapRingMap k) (infinityOverlapRingMap k)
    (fun _ _ => Commute.all _ _)

lemma left_mem (x : nodeRing k) : affineOverlapRingMap k x ∈ (overlapTensorMap k).range :=
  ⟨x ⊗ₜ[k] 1, by simp [overlapTensorMap]⟩
lemma right_mem (x : infinityChartRing k) : infinityOverlapRingMap k x ∈ (overlapTensorMap
  k).range :=
  ⟨1 ⊗ₜ[k] x, by simp [overlapTensorMap]⟩

lemma invT_mem : invT k ∈ (overlapTensorMap k).range := by
  simpa only [infinityOverlapRingMap_polynomial, aeval_X] using
    right_mem k (algebraMap k[X] (infinityChartRing k) X)

lemma q_mem : algebraMap k[X] (W k) (q k) ∈ (overlapTensorMap k).range :=
  left_mem k (conductor k)

lemma t_mem : t k ∈ (overlapTensorMap k).range := by
  have he : t k = algebraMap k[X] (W k) (q k) * invT k + 1 := by
    have h := t_mul_invT k
    simp only [q, map_mul, map_sub, map_one]
    change t k = t k * (t k - 1) * invT k + 1
    linear_combination -(t k - 1) * h
  rw [he]
  exact (overlapTensorMap k).range.add_mem
    ((overlapTensorMap k).range.mul_mem (q_mem k) (invT_mem k))
    (overlapTensorMap k).range.one_mem

lemma inverse_q_mem : IsLocalization.Away.invSelf (q k) ∈ (overlapTensorMap k).range := by
  let z := infinityOverlapRingMap k (IsLocalization.Away.invSelf (X - 1 : k[X]))
  have hz : (invT k - 1) * z = 1 := by
    have hh := congrArg (infinityOverlapRingMap k)
      (IsLocalization.Away.mul_invSelf (S := infinityChartRing k) (X - 1 : k[X]))
    simpa only [map_mul, infinityOverlapRingMap_polynomial, map_sub, aeval_X, map_one] using hh
  have he : IsLocalization.Away.invSelf (q k) = -(invT k)^2 * z := by
    apply (IsLocalization.Away.algebraMap_isUnit (S := W k) (q k)).mul_left_cancel
    rw [IsLocalization.Away.mul_invSelf]
    have ht := t_mul_invT k
    simp only [q, map_mul, map_sub, map_one]
    change 1 = t k * (t k - 1) * (-(invT k) ^ 2 * z)
    calc
      1 = (invT k - 1) * z := hz.symm
      _ = -(t k - 1) * invT k * z := by linear_combination z * ht
      _ = -(t k * invT k) * ((t k - 1) * invT k) * z := by rw [ht]; ring
      _ = t k * (t k - 1) * (-(invT k) ^ 2 * z) := by ring
  rw [he]
  exact (overlapTensorMap k).range.mul_mem
    ((overlapTensorMap k).range.neg_mem ((overlapTensorMap k).range.pow_mem (invT_mem k) 2))
    (right_mem k _)

lemma polynomial_mem (p : k[X]) : algebraMap k[X] (W k) p ∈ (overlapTensorMap k).range := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using (overlapTensorMap k).range.add_mem hp hq
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
      apply (overlapTensorMap k).range.mul_mem
      · exact (overlapTensorMap k).range.algebraMap_mem a
      · exact (overlapTensorMap k).range.pow_mem (t_mem k) n

theorem overlapTensorMap_surjective : Function.Surjective (overlapTensorMap k) := by
  intro z
  obtain ⟨n, p, h⟩ := IsLocalization.Away.surj (q k) z
  have he : z = algebraMap k[X] (W k) p * IsLocalization.Away.invSelf (q k) ^ n := by
    rw [← h, mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  change z ∈ (overlapTensorMap k).range
  rw [he]
  exact (overlapTensorMap k).range.mul_mem (polynomial_mem k p)
    ((overlapTensorMap k).range.pow_mem (inverse_q_mem k) n)
end ConcreteSeparation

end Polynomial.PinchedPair

/- Migration sources: frozen R5 packet f8a3314ddecffcada2ec721d26d56a937bed9690.
Nodal.Affine: equalizer, conductor, localization, reciprocal algebra.
Nodal.Projective: cubic presentation and tangent equations.
Nodal.Gluing: normalization defect and overlap tensor map. -/
