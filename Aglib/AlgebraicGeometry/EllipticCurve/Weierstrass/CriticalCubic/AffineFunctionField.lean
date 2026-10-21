/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.CriticalCubic.AffinePinching
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
Native extraction from the R5 local-model source
`PointedResolution.CriticalCubic.Affine`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`7b96346da695d3620f0eaf7365062370f583852995e6c61c2bebb894bf359293`.
Exactly the 19 previously unconsumed affine finite/localization/fraction-field/section
  declarations. Existing literal equation, coordinateMap and affineNormalization are reused. A
  proved one-power conductor identity removes the original heartbeat override without changing the
  scalar map or conclusion.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
universe u

section ParameterRoots
noncomputable section
open Polynomial
namespace WeierstrassCurve.CriticalCubic
variable (k : Type u) [Field k] (a b : k)
lemma two_roots_discriminant_ne_zero (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    a ^ 2 + 4 * b ≠ 0 := by
  have hp : (r - s) * (r + s + a) = 0 := by
    linear_combination hr - hs
  have ha : a = -(r + s) := eq_neg_of_add_eq_zero_right
    ((mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hrs))
  have hb : b = r ^ 2 + a * r := (sub_eq_zero.mp hr).symm
  have hd : a ^ 2 + 4 * b = (r - s) ^ 2 := by
    rw [hb, ha]
    ring
  rw [hd]
  exact pow_ne_zero 2 (sub_ne_zero.mpr hrs)

lemma parameter_origin_iff (t : k) :
    (xPolynomial k a b).eval t = 0 ∧ (yPolynomial k a b).eval t = 0 ↔
      t ^ 2 + a * t - b = 0 := by
  simp only [xPolynomial, yPolynomial, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  constructor
  · exact And.left
  · intro h
    exact ⟨h, by rw [h, mul_zero]⟩


end WeierstrassCurve.CriticalCubic
end
end ParameterRoots


section CriticalCubicFinite


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
namespace WeierstrassCurve.CriticalCubic
variable (k : Type u) [Field k] (a b : k)

local notation "A" => WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine (equation
  k a b))

/-- The actual parameter is integral over the actual cubic coordinate ring. -/
lemma parameter_isIntegral :
    let := (coordinateMap k a b).toRingHom.toAlgebra
    IsIntegral A (X : k[X]) := by
  let := (coordinateMap k a b).toRingHom.toAlgebra
  let p : A[X] := X ^ 2 + C (algebraMap k A a) * X -
    C (algebraMap k A b) - C (WeierstrassCurve.affineX (equation k a b))
  refine ⟨p, ?_, ?_⟩
  · dsimp [p]
    monicity!
  · simp only [p, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
    change X ^ 2 + coordinateMap k a b (algebraMap k A a) * X -
      coordinateMap k a b (algebraMap k A b) -
      coordinateMap k a b (WeierstrassCurve.affineX (equation k a b)) = 0
    simp [xPolynomial]

lemma parameter_adjoin_top :
    let := (coordinateMap k a b).toRingHom.toAlgebra
    Algebra.adjoin A ({X} : Set k[X]) = ⊤ := by
  let := (coordinateMap k a b).toRingHom.toAlgebra
  apply Subalgebra.restrictScalars_injective k
  rw [Algebra.Subalgebra.restrictScalars_adjoin, Polynomial.adjoin_X, sup_top_eq,
    Subalgebra.restrictScalars_top]

/-- The actual affine parameterization is finite. -/
lemma coordinateMap_finite : (coordinateMap k a b).Finite := by
  let := (coordinateMap k a b).toRingHom.toAlgebra
  have hi := parameter_isIntegral k a b
  have hf := Algebra.finite_adjoin_simple_of_isIntegral hi
  rw [parameter_adjoin_top k a b] at hf
  exact Module.Finite.of_surjective (Subalgebra.val (⊤ : Subalgebra A k[X])).toLinearMap
    (fun p => ⟨⟨p, trivial⟩, rfl⟩)

end WeierstrassCurve.CriticalCubic

end
end CriticalCubicFinite

section CriticalCubicLocalization


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
namespace WeierstrassCurve.CriticalCubic
variable (k : Type u) [Field k] (a b : k)

/-- Clearing powers of x makes every parameter polynomial a genuine cubic function. -/
lemma coordinateMap_clear_denominators (p : k[X]) :
    ∃ z : (equation k a b).toAffine.CoordinateRing, ∃ m : ℕ,
      coordinateMap k a b z = (xPolynomial k a b) ^ m * p := by
  obtain ⟨z, hz⟩ := coordinateMap_preimage_x_mul k a b p
  exact ⟨z, 1, by simpa only [pow_one] using hz⟩

/-- Away from the singular origin, the literal parameterization is an isomorphism. -/
lemma coordinateMap_away_bijective :
    Function.Bijective (Localization.awayMap (coordinateMap k a b).toRingHom
      (WeierstrassCurve.affineX (equation k a b))) := by
  constructor
  · apply Localization.awayMap_injective_iff.mpr
    intro z hz
    refine ⟨0, ?_⟩
    have : z = 0 := (map_eq_zero_iff _ (coordinateMap_injective k a b)).mp hz
    simp [this]
  · apply Localization.awayMap_surjective_iff.mpr
    intro p
    obtain ⟨z, m, hz⟩ := coordinateMap_clear_denominators k a b p
    exact ⟨z, m, by simpa using hz⟩

/-- The actual affine normalization is an isomorphism on the dense x-chart. -/
def coordinateMapAwayEquiv :
    Localization.Away (WeierstrassCurve.affineX (equation k a b)) ≃ₐ[k]
      Localization.Away (coordinateMap k a b
        (WeierstrassCurve.affineX (equation k a b))) :=
  AlgEquiv.ofBijective (Localization.awayMapₐ (coordinateMap k a b)
    (WeierstrassCurve.affineX (equation k a b)))
    (coordinateMap_away_bijective k a b)

@[simp] lemma coordinateMapAwayEquiv_algebraMap
    (z : (equation k a b).toAffine.CoordinateRing) :
    coordinateMapAwayEquiv k a b (algebraMap _ _ z) =
      algebraMap _ _ (coordinateMap k a b z) := by
  simp [coordinateMapAwayEquiv, Localization.awayMapₐ, IsLocalization.Away.mapₐ,
    IsLocalization.Away.map, IsLocalization.map_eq]

/-- The localized inverse parameter is literally y/x. -/
lemma coordinateMapAwayEquiv_inverse_parameter :
    (coordinateMapAwayEquiv k a b).symm (algebraMap k[X] _ X) =
      algebraMap _ _ (WeierstrassCurve.affineY (equation k a b)) *
        IsLocalization.Away.invSelf (WeierstrassCurve.affineX (equation k a b)) := by
  apply (coordinateMapAwayEquiv k a b).injective
  rw [AlgEquiv.apply_symm_apply, map_mul, coordinateMapAwayEquiv_algebraMap,
    coordinateMap_Y, yPolynomial, map_mul]
  have h := congrArg (coordinateMapAwayEquiv k a b)
    (IsLocalization.Away.mul_invSelf
      (S := Localization.Away (WeierstrassCurve.affineX (equation k a b)))
      (WeierstrassCurve.affineX (equation k a b)))
  simp only [map_mul, map_one, coordinateMapAwayEquiv_algebraMap, coordinateMap_X] at h
  rw [mul_assoc, h, mul_one]

end WeierstrassCurve.CriticalCubic

end
end CriticalCubicLocalization

section CriticalCubicNormalization


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
namespace WeierstrassCurve.CriticalCubic
variable (k : Type u) [Field k] (a b : k)
local notation "A" => WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine (equation
  k a b))
local notation "K" => FractionRing k[X]

/-- The fixed embedding into the parameter function field. -/
def fractionCoordinateMap : A →+* K :=
  (algebraMap k[X] K).comp (coordinateMap k a b).toRingHom

lemma fractionCoordinateMap_injective : Function.Injective (fractionCoordinateMap k a b) :=
  (IsFractionRing.injective k[X] K).comp (coordinateMap_injective k a b)

/-- The same field is the fraction field of the actual cubic.
The existing one-power conductor identity supplies the common denominator. -/
lemma coordinateMap_isFractionRing :
    let := (coordinateMap k a b).toRingHom.toAlgebra
    IsFractionRing A K := by
  let := (coordinateMap k a b).toRingHom.toAlgebra
  let : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr
    (fractionCoordinateMap_injective k a b)
  apply IsFractionRing.of_field
  intro z
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective k[X] z
  obtain ⟨v, hv⟩ := coordinateMap_preimage_x_mul k a b p
  obtain ⟨w, hw⟩ := coordinateMap_preimage_x_mul k a b q
  refine ⟨v, w, ?_⟩
  change algebraMap k[X] K p / algebraMap k[X] K q =
    fractionCoordinateMap k a b v / fractionCoordinateMap k a b w
  change algebraMap k[X] K p / algebraMap k[X] K q =
    algebraMap k[X] K (coordinateMap k a b v) /
      algebraMap k[X] K (coordinateMap k a b w)
  rw [hv, hw, map_mul, map_mul]
  have hx : algebraMap k[X] K (xPolynomial k a b) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] K)).mpr
      (xPolynomial_ne_zero k a b)
  exact (mul_div_mul_left _ _ hx).symm

/-- The parameter polynomial ring is the integral closure in the same fraction field. -/
lemma coordinateMap_isIntegralClosure :
    let := (coordinateMap k a b).toRingHom.toAlgebra
    IsIntegralClosure k[X] A K := by
  let := (coordinateMap k a b).toRingHom.toAlgebra
  let : Module.Finite A k[X] := coordinateMap_finite k a b
  exact IsIntegralClosure.of_isIntegrallyClosed k[X] A K

end WeierstrassCurve.CriticalCubic

end
end CriticalCubicNormalization

section AffineGeometry
noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace WeierstrassCurve.CriticalCubic
variable (k : Type u) [Field k] (a b : k)
local notation "A" => WeierstrassCurve.Affine.CoordinateRing
  (WeierstrassCurve.toAffine (equation k a b))
instance affineNormalization_finite : IsFinite (affineNormalization k a b) :=
  (IsFinite.SpecMap_iff _).mpr (coordinateMap_finite k a b)

instance affineNormalization_proper : IsProper (affineNormalization k a b) := inferInstance

instance affineNormalization_dominant : IsDominant (affineNormalization k a b) := by
  constructor
  change DenseRange (PrimeSpectrum.comap (coordinateMap k a b).toRingHom)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  intro z hz
  have hz0 : z = 0 := (map_eq_zero_iff _ (coordinateMap_injective k a b)).mp hz
  rw [hz0]
  exact Ideal.zero_mem _


lemma parameterSection_injective : Function.Injective (parameterSection k) := by
  intro r s h
  have he := Spec.map_injective h
  have hx := congrArg (fun f : CommRingCat.of k[X] ⟶ CommRingCat.of k => f.hom X) he
  simpa using hx

/-- Distinct actual rational preimages force the ordinary-node tangent discriminant. -/
lemma two_parameterSections_discriminant_ne_zero (r s : k)
    (hrs : parameterSection k r ≠ parameterSection k s)
    (hr : parameterSection k r ≫ affineNormalization k a b = originSection k a b)
    (hs : parameterSection k s ≫ affineNormalization k a b = originSection k a b) :
    a ^ 2 + 4 * b ≠ 0 :=
  two_roots_discriminant_ne_zero k a b r s (fun h => hrs (congrArg _ h))
    ((parameterSection_comp_eq_origin_iff k a b r).mp hr)
    ((parameterSection_comp_eq_origin_iff k a b s).mp hs)


end WeierstrassCurve.CriticalCubic
end
end AffineGeometry
