/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.Geometry
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.BaseChange
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
public import Aglib.RingTheory.IntegralClosure.PrimeAway
public import Aglib.RingTheory.DiscreteValuationRing.FractionAway
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Normality of the literal Weierstrass cubic over a DVR

The generic discriminant is the only condition on the equation. The two
actual monic charts have integral special fibres; their scalar uniformizer
is therefore prime. Generic smoothness gives normal generic charts, and the
prime-away criterion proves normality of the original chart rings.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct nonZeroDivisors
universe u

namespace WeierstrassCurve.Projective

/-- Smoothness of an actual affine scheme over a field implies that its
domain coordinate ring is integrally closed. -/
theorem coordinateRing_integrallyClosed_of_smoothSpec
    (k A : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    (h : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k A)))) : IsIntegrallyClosed A := by
  let X := Spec (.of A)
  let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) :=
    (Scheme.smoothFieldNormality k X _ h x).2
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  let : IsIntegrallyClosed Γ(X, ⊤) :=
    Scheme.isIntegrallyClosed_sections_of_isAffineOpen X ⊤ (isAffineOpen_top _)
  exact IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv

/-- The original affine chart of a nonsingular field cubic is normal. -/
theorem affineRing_integrallyClosed (k : Type u) [Field k]
    (W : WeierstrassCurve k) (hΔ : W.Δ ≠ 0) : IsIntegrallyClosed (affineRing W) := by
  let : SmoothOfRelativeDimension 1 (structureMap W) := structureMap_smoothOne W hΔ
  let : Smooth (structureMap W) := SmoothOfRelativeDimension.smooth 1 _
  apply coordinateRing_integrallyClosed_of_smoothSpec k
  have h : Smooth (affineChart W ≫ structureMap W) := inferInstance
  rwa [affineChart_structure W] at h

/-- The original infinity chart of a nonsingular field cubic is normal. -/
theorem infinityRing_integrallyClosed (k : Type u) [Field k]
    (W : WeierstrassCurve k) (hΔ : W.Δ ≠ 0) : IsIntegrallyClosed (infinityRing W) := by
  let : IsDomain (infinityRing W) := infinityRing_isDomain_of_isDomain W
  let : SmoothOfRelativeDimension 1 (structureMap W) := structureMap_smoothOne W hΔ
  let : Smooth (structureMap W) := SmoothOfRelativeDimension.smooth 1 _
  apply coordinateRing_integrallyClosed_of_smoothSpec k
  have h : Smooth (infinityAffineChart W ≫ structureMap W) := inferInstance
  rwa [infinityAffineChart_structure W] at h

section DVRAlgebra

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (F : Type u) [Field F] [Algebra R F] [IsFractionRing R F]
variable (A : Type u) [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A]

/-- For a faithful domain algebra over a DVR, an integral special fibre and
a normal generic fibre give normality, through a prime scalar uniformizer. -/
theorem dvrAlgebra_integrallyClosed
    [IsDomain (IsLocalRing.ResidueField R ⊗[R] A)]
    [IsIntegrallyClosed (F ⊗[R] A)] : IsIntegrallyClosed A := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let p : A := algebraMap R A π
  have hp0 : p ≠ 0 := by
    simpa only [p, map_zero] using (FaithfulSMul.algebraMap_injective R A).ne hπ.ne_zero
  have hI : (IsLocalRing.maximalIdeal R).map (algebraMap R A) = Ideal.span {p} := by
    rw [hπ.maximalIdeal_eq]
    simp only [Ideal.map_span, Set.image_singleton, p]
  let e : (A ⧸ Ideal.span {p}) ≃+* (IsLocalRing.ResidueField R ⊗[R] A) :=
    (Ideal.quotientEquivAlgOfEq A hI.symm).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A (IsLocalRing.maximalIdeal R)).toRingEquiv
  let : IsDomain (A ⧸ Ideal.span {p}) := e.toMulEquiv.isDomain _
  have hp : Prime p := (Ideal.span_singleton_prime hp0).mp
    ((Ideal.Quotient.isDomain_iff_prime _).mp inferInstance)
  let : IsLocalization.Away π F :=
    IsDiscreteValuationRing.isLocalizationAway_of_nonzero_nonunit F hπ.ne_zero hπ.not_isUnit
  let : Algebra A (F ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  let : IsLocalization.Away p (F ⊗[R] A) := by
    change IsLocalization.Away (algebraMap R A π) (F ⊗[R] A)
    infer_instance
  exact IsIntegrallyClosed.of_isLocalizationAway_prime (F ⊗[R] A) hp

end DVRAlgebra

section DVR

variable {R F : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field F] [Algebra R F] [IsFractionRing R F]
variable (W : WeierstrassCurve R) (hΔ : (W.baseChange F).Δ ≠ 0)

include hΔ

/-- Normality of the actual affine chart over the original DVR. -/
theorem affineRing_integrallyClosed_of_generic_discriminant :
    IsIntegrallyClosed (affineRing W) := by
  let : IsIntegrallyClosed (W.map (algebraMap R F)).toAffine.CoordinateRing :=
    affineRing_integrallyClosed F _ hΔ
  let : IsIntegrallyClosed (F ⊗[R] affineRing W) :=
    IsIntegrallyClosed.of_equiv (WeierstrassCurve.affineTensorEquiv F W).toRingEquiv.symm
  let : IsDomain (IsLocalRing.ResidueField R ⊗[R] affineRing W) :=
    (WeierstrassCurve.affineTensorEquiv (IsLocalRing.ResidueField R) W).toMulEquiv.isDomain _
  exact dvrAlgebra_integrallyClosed (R := R) F (affineRing W)

/-- Normality of the actual infinity chart over the original DVR. -/
theorem infinityRing_integrallyClosed_of_generic_discriminant :
    IsIntegrallyClosed (infinityRing W) := by
  let : IsDomain (infinityRing W) := infinityRing_isDomain_of_isDomain W
  let : IsIntegrallyClosed (infinityRing (W.baseChange F)) :=
    infinityRing_integrallyClosed F _ hΔ
  let : IsIntegrallyClosed (F ⊗[R] infinityRing W) :=
    IsIntegrallyClosed.of_equiv (infinityRingBaseChangeEquiv (S := F) W).toRingEquiv.symm
  let : IsDomain (infinityRing (W.baseChange (IsLocalRing.ResidueField R))) :=
    infinityRing_isDomain_of_isDomain _
  let : IsDomain (IsLocalRing.ResidueField R ⊗[R] infinityRing W) :=
    (infinityRingBaseChangeEquiv (S := IsLocalRing.ResidueField R) W).toMulEquiv.isDomain _
  exact dvrAlgebra_integrallyClosed (R := R) F (infinityRing W)

/-- The same literal homogeneous-quotient cubic has normal actual stalks.
Only the nonzero generic discriminant is required of the equation. -/
theorem normalStalks_of_generic_discriminant : Scheme.NormalStalks (scheme W) := by
  let : IsIntegrallyClosed (affineRing W) :=
    affineRing_integrallyClosed_of_generic_discriminant W hΔ
  let : IsDomain (infinityRing W) := infinityRing_isDomain_of_isDomain W
  let : IsIntegrallyClosed (infinityRing W) :=
    infinityRing_integrallyClosed_of_generic_discriminant W hΔ
  intro x
  have hx : x ∈ (infinityAffineChart W).opensRange ⊔ (affineChart W).opensRange := by
    rw [infinity_affine_cover]
    trivial
  rcases hx with hx | hx
  · obtain ⟨p, rfl⟩ := hx
    let : IsIntegrallyClosed ((Spec (.of (infinityRing W))).presheaf.stalk p) :=
      (Scheme.isIntegrallyClosed_and_isDomain_stalk_Spec (infinityRing W) p).1
    let : IsDomain ((Spec (.of (infinityRing W))).presheaf.stalk p) :=
      (Scheme.isIntegrallyClosed_and_isDomain_stalk_Spec (infinityRing W) p).2
    let e := (asIso ((infinityAffineChart W).stalkMap p)).symm.commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  · obtain ⟨p, rfl⟩ := hx
    let : IsIntegrallyClosed ((Spec (.of (affineRing W))).presheaf.stalk p) :=
      (Scheme.isIntegrallyClosed_and_isDomain_stalk_Spec (affineRing W) p).1
    let : IsDomain ((Spec (.of (affineRing W))).presheaf.stalk p) :=
      (Scheme.isIntegrallyClosed_and_isDomain_stalk_Spec (affineRing W) p).2
    let e := (asIso ((affineChart W).stalkMap p)).symm.commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

end DVR

/-- Native correspondence of the original `IntegralWeierstrassNormality`
interface in R5 `CyclicModelComparison/PresentationMaps.lean:539`. -/
def IntegralWeierstrassNormality : Prop :=
  ∀ (R F : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (W : WeierstrassCurve R), (W.baseChange F).Δ ≠ 0 → Scheme.NormalStalks (scheme W)

/-- The exact arbitrary-DVR normality family for the original literal model. -/
theorem integralWeierstrassNormality : IntegralWeierstrassNormality.{u} := by
  intro R F _ _ _ _ _ _ W hΔ
  exact normalStalks_of_generic_discriminant W hΔ

end WeierstrassCurve.Projective
