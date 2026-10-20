/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/Length/PrincipalIntersection.lean` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`1c6f6cfd372b38fa6759dd558cc9550f1c60c10a93d43427bf9b1a6285393a46`.
-/

@[expose] public section

noncomputable section
open IsLocalRing
namespace Ideal
section PrincipalIntersections

variable (R : Type*) [CommRing R]

/-- The actual ideal image in the actual quotient by the common ideal. -/
def quotientIdealImage (I J : Ideal R) : Submodule R (R ⧸ I) :=
  Submodule.map (Submodule.mkQ (I : Submodule R R)) (J : Submodule R R)

/-- The canonical quotient sequence computes the common-ideal colength. -/
theorem length_quotient_eq_image_add (I J : Ideal R) (h : I ≤ J) :
    Module.length R (R ⧸ I) =
      Module.length R (quotientIdealImage R I J) + Module.length R (R ⧸ J) := by
  let W := quotientIdealImage R I J
  let g : (R ⧸ I) →ₗ[R] (R ⧸ J) := Submodule.factor h
  have he : Function.Exact W.subtype g := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
    simp [g, W, quotientIdealImage, Submodule.mapQ, Submodule.ker_liftQ, Submodule.ker_mkQ]
  exact Module.length_eq_add_of_exact W.subtype g (Submodule.subtype_injective _)
    (Submodule.factor_surjective h) he

variable [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]

/-- The intersection of the two actual principal ideals has finite colength. -/
theorem principalIntersection_finiteLength (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    IsFiniteLength R (R ⧸ (Ideal.span {a} ⊓ Ideal.span {b})) := by
  have h : Ideal.span {a * b} ≤ Ideal.span {a} ⊓ Ideal.span {b} := by
    apply le_inf
    · exact Ideal.span_singleton_le_span_singleton.mpr ⟨b, rfl⟩
    · exact Ideal.span_singleton_le_span_singleton.mpr ⟨a, mul_comm _ _⟩
  exact (isFiniteLength_quotient_span_singleton R
    (mem_nonZeroDivisors_iff_ne_zero.mpr (mul_ne_zero ha hb))).of_surjective
      (Submodule.factor_surjective h)

/-- The finite quotient images of numerator and denominator ideals have the
signed length difference used by the common fractional-ideal intersection route. -/
theorem principalIntersection_image_length_difference
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    ((Module.length R (quotientIdealImage R (Ideal.span {a} ⊓ Ideal.span {b})
        (Ideal.span {b}))).toNat : ℤ) -
      ((Module.length R (quotientIdealImage R (Ideal.span {a} ⊓ Ideal.span {b})
        (Ideal.span {a}))).toNat : ℤ) =
      ((Module.length R (R ⧸ Ideal.span {a})).toNat : ℤ) -
        ((Module.length R (R ⧸ Ideal.span {b})).toNat : ℤ) := by
  have hfin := principalIntersection_finiteLength R a b ha hb
  have hA := length_quotient_eq_image_add R (Ideal.span {a} ⊓ Ideal.span {b})
    (Ideal.span {a}) inf_le_left
  have hB := length_quotient_eq_image_add R (Ideal.span {a} ⊓ Ideal.span {b})
    (Ideal.span {b}) inf_le_right
  have hiA := hfin.of_injective
    (Submodule.subtype_injective (quotientIdealImage R (Ideal.span {a} ⊓ Ideal.span {b})
      (Ideal.span {a})))
  have hiB := hfin.of_injective
    (Submodule.subtype_injective (quotientIdealImage R (Ideal.span {a} ⊓ Ideal.span {b})
      (Ideal.span {b})))
  have hqA := isFiniteLength_quotient_span_singleton R
    (mem_nonZeroDivisors_iff_ne_zero.mpr ha)
  have hqB := isFiniteLength_quotient_span_singleton R
    (mem_nonZeroDivisors_iff_ne_zero.mpr hb)
  have hnA := congrArg ENat.toNat hA
  have hnB := congrArg ENat.toNat hB
  rw [ENat.toNat_add (Module.length_ne_top_iff.mpr hiA)
    (Module.length_ne_top_iff.mpr hqA)] at hnA
  rw [ENat.toNat_add (Module.length_ne_top_iff.mpr hiB)
    (Module.length_ne_top_iff.mpr hqB)] at hnB
  omega

end PrincipalIntersections
end Ideal
