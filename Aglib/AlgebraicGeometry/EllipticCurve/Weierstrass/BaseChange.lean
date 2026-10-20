/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.InfinityChart
public import Aglib.AlgebraicGeometry.AffineScheme.TensorPullback
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Coefficient base change of the projective Weierstrass cubic

The actual coefficient ring homomorphism induces a map on the fixed
homogeneous Proj. Its same infinity and affine charts give the literal
Cartesian comparison, with both projections and the pointed section explicit.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Polynomial TensorProduct
universe u v

namespace WeierstrassCurve.Projective

open MvPolynomial
variable {R S : Type u} [CommRing R] [CommRing S]

lemma projectivePolynomial_map (W : WeierstrassCurve R) (f : R →+* S) :
    MvPolynomial.map f W.toProjective.polynomial = (W.map f).toProjective.polynomial := by
  simp [WeierstrassCurve.Projective.polynomial, WeierstrassCurve.map]

/-- Actual coefficient map on the existing homogeneous quotients. -/
def homogeneousCoefficientMap (W : WeierstrassCurve R) (f : R →+* S) :
    homogeneousCoordinateRing W →+* homogeneousCoordinateRing (W.map f) :=
  Ideal.quotientMap _ (MvPolynomial.map f) (by
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    change MvPolynomial.map f W.toProjective.polynomial ∈ cubicIdeal (W.map f)
    rw [projectivePolynomial_map]
    exact Ideal.subset_span (Set.mem_singleton _))

@[simp] lemma homogeneousCoefficientMap_mk (W : WeierstrassCurve R) (f : R →+* S)
    (p : MvPolynomial (Fin 3) R) :
    homogeneousCoefficientMap W f (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.map f p) := rfl

@[simp] lemma homogeneousCoefficientMap_coordinate (W : WeierstrassCurve R)
    (f : R →+* S) (i : Fin 3) :
    homogeneousCoefficientMap W f (coordinate W i) = coordinate (W.map f) i := by
  simp [coordinate]

@[simp] lemma homogeneousCoefficientMap_constant (W : WeierstrassCurve R)
    (f : R →+* S) (a : R) :
    homogeneousCoefficientMap W f (algebraMap R (homogeneousCoordinateRing W) a) =
      algebraMap S (homogeneousCoordinateRing (W.map f)) (f a) := by
  change homogeneousCoefficientMap W f (Ideal.Quotient.mk _ (C a)) = _
  simp
  rfl

/-- The coefficient morphism preserves the literal quotient grading. -/
def gradedCoefficientMap (W : WeierstrassCurve R) (f : R →+* S) :
    grading W →+*ᵍ grading (W.map f) where
  __ := homogeneousCoefficientMap W f
  map_mem := by
    intro n a ha
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp ha
    exact Submodule.mem_map.mpr ⟨MvPolynomial.map f p, hp.map f, rfl⟩

lemma irrelevant_le_span_coordinates (W : WeierstrassCurve R) :
    (HomogeneousIdeal.irrelevant (grading W)).toIdeal ≤ Ideal.span (Set.range (coordinate W)) := by
  intro x hx
  convert_to x - GradedRing.projZeroRingHom (grading W) x ∈ _
  · rw [GradedRing.projZeroRingHom_apply, ← GradedRing.proj_apply,
      (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hx, sub_zero]
  clear hx
  have hx : x ∈ Algebra.adjoin (grading W 0) (Set.range (coordinate W)) := by
    rw [coordinate_generate]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [GradedRing.projZeroRingHom_apply,
      DirectSum.decompose_of_mem_ne (grading W) (coordinate_mem W i) (by decide), sub_zero]
    exact Ideal.subset_span ⟨i, rfl⟩
  | algebraMap r =>
    convert! zero_mem (Ideal.span _)
    rw [sub_eq_zero]
    exact (DirectSum.decompose_of_mem_same (grading W) r.2).symm
  | add x y hx hy ihx ihy =>
    rw [map_add, add_sub_add_comm]
    exact add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
    convert! add_mem (Ideal.mul_mem_left _ x ihy)
      (Ideal.mul_mem_right (GradedRing.projZeroRingHom (grading W) y) _ ihx) using 1
    rw [map_mul]
    ring

lemma irrelevant_le_map_coefficient (W : WeierstrassCurve R) (f : R →+* S) :
    HomogeneousIdeal.irrelevant (grading (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (grading W)).map (gradedCoefficientMap W f) := by
  change (HomogeneousIdeal.irrelevant (grading (W.map f))).toIdeal ≤
    (HomogeneousIdeal.irrelevant (grading W)).toIdeal.map (gradedCoefficientMap W f)
  apply (irrelevant_le_span_coordinates (W.map f)).trans
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  rw [← homogeneousCoefficientMap_coordinate W f i]
  exact Ideal.mem_map_of_mem (gradedCoefficientMap W f)
    (HomogeneousIdeal.mem_irrelevant_of_mem (grading W) (by decide : 0 < 1) (coordinate_mem W i))

/-- The genuine coefficient morphism between the fixed projective Weierstrass schemes. -/
def coefficientSchemeMap (W : WeierstrassCurve R) (f : R →+* S) :
    scheme (W.map f) ⟶ scheme W :=
  Proj.map (gradedCoefficientMap W f) (irrelevant_le_map_coefficient W f)

@[simp] lemma coefficientSchemeMap_preimage_basicOpen (W : WeierstrassCurve R)
    (f : R →+* S) (i : Fin 3) :
    coefficientSchemeMap W f ⁻¹ᵁ Proj.basicOpen (grading W) (coordinate W i) =
      Proj.basicOpen (grading (W.map f)) (coordinate (W.map f) i) := by
  rw [coefficientSchemeMap, Proj.map_preimage_basicOpen]
  change Proj.basicOpen _ (homogeneousCoefficientMap W f (coordinate W i)) = _
  rw [homogeneousCoefficientMap_coordinate]

lemma coefficient_powers_le (W : WeierstrassCurve R) (f : R →+* S) (i : Fin 3) :
    Submonoid.powers (coordinate W i) ≤
      (Submonoid.powers (coordinate (W.map f) i)).comap (gradedCoefficientMap W f) := by
  apply Submonoid.powers_le.mpr
  change homogeneousCoefficientMap W f (coordinate W i) ∈
    Submonoid.powers (coordinate (W.map f) i)
  rw [homogeneousCoefficientMap_coordinate]
  exact Submonoid.mem_powers _

/-- Native degree-zero localization map, with no transported chart chosen. -/
def chartCoefficientMap (W : WeierstrassCurve R) (f : R →+* S) (i : Fin 3) :
    chartRing W i →+* chartRing (W.map f) i :=
  HomogeneousLocalization.map (gradedCoefficientMap W f) (coefficient_powers_le W f i)

@[simp] lemma chartCoefficientMap_normalizedCoordinate (W : WeierstrassCurve R)
    (f : R →+* S) (i j : Fin 3) :
    chartCoefficientMap W f i (normalizedCoordinate W i j) =
      normalizedCoordinate (W.map f) i j := by
  apply HomogeneousLocalization.val_injective
  simp [chartCoefficientMap, normalizedCoordinate, HomogeneousLocalization.Away.mk,
    HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
    gradedCoefficientMap, homogeneousCoefficientMap_coordinate]

@[simp] lemma chartCoefficientMap_constant (W : WeierstrassCurve R)
    (f : R →+* S) (i : Fin 3) (a : R) :
    chartCoefficientMap W f i (chartConstant W i a) = chartConstant (W.map f) i (f a) := by
  apply HomogeneousLocalization.val_injective
  simp [chartCoefficientMap, chartConstant, HomogeneousLocalization.fromZeroRingHom,
    HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
    gradedCoefficientMap, constToGradeZero, homogeneousCoefficientMap_constant]

lemma chartCoefficientMap_spec (W : WeierstrassCurve R) (f : R →+* S) (i : Fin 3) :
    chart (W.map f) i ≫ coefficientSchemeMap W f =
      Spec.map (CommRingCat.ofHom (chartCoefficientMap W f i)) ≫ chart W i := by
  have h : (gradedCoefficientMap W f) (coordinate W i) = coordinate (W.map f) i :=
    homogeneousCoefficientMap_coordinate W f i
  have hgen (t : homogeneousCoordinateRing (W.map f))
      (ht : t ∈ grading (W.map f) 1)
      (heq : (gradedCoefficientMap W f) (coordinate W i) = t) :
      Proj.awayι (grading (W.map f)) t ht (by decide) ≫ coefficientSchemeMap W f =
        Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.map (gradedCoefficientMap W f)
            (P := Submonoid.powers (coordinate W i)) (Q := Submonoid.powers t)
            (by
              apply Submonoid.powers_le.mpr
              change (gradedCoefficientMap W f) (coordinate W i) ∈ Submonoid.powers t
              rw [heq]
              exact Submonoid.mem_powers _))) ≫ chart W i := by
    subst t
    exact Proj.awayι_comp_map (gradedCoefficientMap W f) (irrelevant_le_map_coefficient W f)
      (by decide) (coordinate W i) (coordinate_mem W i)
  exact hgen _ (coordinate_mem (W.map f) i) h

/-- The chart projection triangle over an arbitrary commutative ring. -/
@[reassoc] lemma chart_structure_ring (W : WeierstrassCurve R) (i : Fin 3) :
    chart W i ≫ structureMap W = Spec.map (CommRingCat.ofHom (chartConstant W i)) := by
  rw [chart, structureMap, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

@[reassoc] lemma chart_coefficient_structure (W : WeierstrassCurve R)
    (f : R →+* S) (i : Fin 3) :
    chart (W.map f) i ≫ coefficientSchemeMap W f ≫ structureMap W =
      chart (W.map f) i ≫ structureMap (W.map f) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [← Category.assoc, chartCoefficientMap_spec, Category.assoc, chart_structure_ring,
    ← Category.assoc, chart_structure_ring, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact chartCoefficientMap_constant W f i a

/-- The coefficient morphism lies over the literal induced map of affine bases. -/
@[reassoc] theorem coefficientSchemeMap_structure (W : WeierstrassCurve R) (f : R →+* S) :
    coefficientSchemeMap W f ≫ structureMap W =
      structureMap (W.map f) ≫ Spec.map (CommRingCat.ofHom f) := by
  apply (monicChartCover (W.map f)).hom_ext
  intro b
  cases b
  · change (Spec.map _ ≫ chart (W.map f) 1) ≫ _ = (Spec.map _ ≫ chart (W.map f) 1) ≫ _
    simp only [Category.assoc, chart_coefficient_structure]
  · change (Spec.map _ ≫ chart (W.map f) 2) ≫ _ = (Spec.map _ ≫ chart (W.map f) 2) ≫ _
    simp only [Category.assoc, chart_coefficient_structure]

end WeierstrassCurve.Projective

namespace WeierstrassCurve.Projective

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The coefficient map of the explicit infinity ring, induced by the native Proj map. -/
def infinityCoefficientMap (W : WeierstrassCurve R) (f : R →+* S) :
    infinityRing W →+* infinityRing (W.map f) :=
  (fromInfinityProjectiveChart (W.map f)).comp
    ((chartCoefficientMap W f 1).comp (toInfinityProjectiveChart W))

/-- The coefficient map of the existing affine ring, induced by the native Proj map. -/
def affineCoefficientMap (W : WeierstrassCurve R) (f : R →+* S) :
    affineRing W →+* affineRing (W.map f) :=
  (fromProjectiveChart (W.map f)).comp
    ((chartCoefficientMap W f 2).comp (toProjectiveChart W))

@[simp] lemma infinityCoefficientMap_u (W : WeierstrassCurve R) (f : R →+* S) :
    infinityCoefficientMap W f (infinityU W) = infinityU (W.map f) := by
  simp [infinityCoefficientMap]
@[simp] lemma infinityCoefficientMap_v (W : WeierstrassCurve R) (f : R →+* S) :
    infinityCoefficientMap W f (infinityV W) = infinityV (W.map f) := by
  simp [infinityCoefficientMap]
@[simp] lemma infinityCoefficientMap_constant (W : WeierstrassCurve R)
    (f : R →+* S) (a : R) :
    infinityCoefficientMap W f (algebraMap R (infinityRing W) a) =
      algebraMap S (infinityRing (W.map f)) (f a) := by
  simp [infinityCoefficientMap]

@[simp] lemma affineCoefficientMap_x (W : WeierstrassCurve R) (f : R →+* S) :
    affineCoefficientMap W f (affineX W) = affineX (W.map f) := by
  simp [affineCoefficientMap]
@[simp] lemma affineCoefficientMap_y (W : WeierstrassCurve R) (f : R →+* S) :
    affineCoefficientMap W f (affineY W) = affineY (W.map f) := by
  simp [affineCoefficientMap]
@[simp] lemma affineCoefficientMap_constant (W : WeierstrassCurve R)
    (f : R →+* S) (a : R) :
    affineCoefficientMap W f (algebraMap R (affineRing W) a) =
      algebraMap S (affineRing (W.map f)) (f a) := by
  simp [affineCoefficientMap]

section Tensor
variable [Algebra R S]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma infinityRingBaseChangeEquiv_includeRight (W : WeierstrassCurve R) :
    (infinityRingBaseChangeEquiv (S := S) W).toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight : infinityRing W →ₐ[R] S ⊗[R] infinityRing W).toRingHom =
        infinityCoefficientMap W (algebraMap R S) := by
  set_option backward.isDefEq.respectTransparency false in
    apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      change infinityRingBaseChangeEquiv W (1 ⊗ₜ[R] AdjoinRoot.of _ (Polynomial.C r)) = _
      simp only [infinityRingBaseChangeEquiv, WeierstrassCurve.baseChange]
      rw [AdjoinRoot.bivariateTensorEquiv_of, Polynomial.map_C]
      exact (infinityCoefficientMap_constant W (algebraMap R S) r).symm
    · change infinityRingBaseChangeEquiv W (1 ⊗ₜ[R] AdjoinRoot.of _ Polynomial.X) = _
      simp only [infinityRingBaseChangeEquiv, WeierstrassCurve.baseChange]
      rw [AdjoinRoot.bivariateTensorEquiv_of, Polynomial.map_X]
      exact (infinityCoefficientMap_v W (algebraMap R S)).symm
  · change infinityRingBaseChangeEquiv W (1 ⊗ₜ[R] AdjoinRoot.root _) = _
    simp only [infinityRingBaseChangeEquiv, WeierstrassCurve.baseChange]
    rw [AdjoinRoot.bivariateTensorEquiv_root]
    exact (infinityCoefficientMap_u W (algebraMap R S)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma affineTensorEquiv_includeRight (W : WeierstrassCurve R) :
    (WeierstrassCurve.affineTensorEquiv S W).toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight : affineRing W →ₐ[R] S ⊗[R] affineRing W).toRingHom =
        affineCoefficientMap W (algebraMap R S) := by
  set_option backward.isDefEq.respectTransparency false in
    apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      change WeierstrassCurve.affineTensorEquiv S W (1 ⊗ₜ[R] AdjoinRoot.of _ (Polynomial.C r)) = _
      simp only [WeierstrassCurve.affineTensorEquiv]
      rw [AdjoinRoot.bivariateTensorEquiv_of, Polynomial.map_C]
      exact (affineCoefficientMap_constant W (algebraMap R S) r).symm
    · change WeierstrassCurve.affineTensorEquiv S W (1 ⊗ₜ[R] AdjoinRoot.of _ Polynomial.X) = _
      simp only [WeierstrassCurve.affineTensorEquiv]
      rw [AdjoinRoot.bivariateTensorEquiv_of, Polynomial.map_X]
      exact (affineCoefficientMap_x W (algebraMap R S)).symm
  · change WeierstrassCurve.affineTensorEquiv S W (1 ⊗ₜ[R] AdjoinRoot.root _) = _
    simp only [WeierstrassCurve.affineTensorEquiv]
    rw [AdjoinRoot.bivariateTensorEquiv_root]
    exact (affineCoefficientMap_y W (algebraMap R S)).symm
end Tensor

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc] lemma infinityAffineChart_coefficient (W : WeierstrassCurve R) (f : R →+* S) :
    infinityAffineChart (W.map f) ≫ coefficientSchemeMap W f =
      Spec.map (CommRingCat.ofHom (infinityCoefficientMap W f)) ≫ infinityAffineChart W := by
  simp only [infinityAffineChart]
  rw [Category.assoc, chartCoefficientMap_spec, ← Category.assoc, ← Spec.map_comp,
    ← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  simp only [infinityCoefficientMap, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
    RingHom.comp_apply, to_fromInfinityProjectiveChart]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc] lemma affineChart_coefficient (W : WeierstrassCurve R) (f : R →+* S) :
    affineChart (W.map f) ≫ coefficientSchemeMap W f =
      Spec.map (CommRingCat.ofHom (affineCoefficientMap W f)) ≫ affineChart W := by
  simp only [affineChart]
  rw [Category.assoc, chartCoefficientMap_spec, ← Category.assoc, ← Spec.map_comp,
    ← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  simp only [affineCoefficientMap, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
    RingHom.comp_apply, to_fromProjectiveChart]

lemma infinityAffineChart_isPullback (W : WeierstrassCurve R) (f : R →+* S) :
    IsPullback (Spec.map (CommRingCat.ofHom (infinityCoefficientMap W f)))
      (infinityAffineChart (W.map f)) (infinityAffineChart W) (coefficientSchemeMap W f) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (infinityAffineChart_coefficient W f)
  rw [infinityAffineChart_range, infinityAffineChart_range,
    coefficientSchemeMap_preimage_basicOpen]

lemma affineChart_isPullback (W : WeierstrassCurve R) (f : R →+* S) :
    IsPullback (Spec.map (CommRingCat.ofHom (affineCoefficientMap W f)))
      (affineChart (W.map f)) (affineChart W) (coefficientSchemeMap W f) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (affineChart_coefficient W f)
  rw [affineChart_range, affineChart_range, coefficientSchemeMap_preimage_basicOpen]

end WeierstrassCurve.Projective

namespace WeierstrassCurve.Projective

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]


variable (W : WeierstrassCurve R)

lemma infinityCoefficientBase_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (infinityCoefficientMap W (algebraMap R S))))
      (infinityAffineChart (W.baseChange S) ≫ structureMap (W.baseChange S))
      (infinityAffineChart W ≫ structureMap W)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  rw [infinityAffineChart_structure, infinityAffineChart_structure]
  exact Spec.isPullback_of_tensorEquiv (infinityRingBaseChangeEquiv W) _
    (infinityRingBaseChangeEquiv_includeRight W)

lemma affineCoefficientBase_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (affineCoefficientMap W (algebraMap R S))))
      (affineChart (W.baseChange S) ≫ structureMap (W.baseChange S))
      (affineChart W ≫ structureMap W)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  rw [affineChart_structure, affineChart_structure]
  exact Spec.isPullback_of_tensorEquiv (WeierstrassCurve.affineTensorEquiv S W) _
    (affineTensorEquiv_includeRight W)

/-- The literal coefficient cubic is the actual pullback over the coefficient ring map. -/
theorem coefficientBaseChange_isPullback :
    IsPullback (coefficientSchemeMap W (algebraMap R S)) (structureMap (W.baseChange S))
      (structureMap W) (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (monicChartCover W)
  intro b
  cases b
  · change IsPullback (pullback.snd _ (infinityAffineChart W))
      (pullback.fst _ (infinityAffineChart W) ≫ structureMap (W.baseChange S))
      (infinityAffineChart W ≫ structureMap W) _
    let H := (infinityAffineChart_isPullback W (algebraMap R S)).flip
    apply (infinityCoefficientBase_isPullback (S := S) W).of_iso H.isoPullback
      (.refl _) (.refl _) (.refl _)
    · simp [WeierstrassCurve.baseChange]
    · simp [WeierstrassCurve.baseChange]
    · simp
    · simp
  · change IsPullback (pullback.snd _ (affineChart W))
      (pullback.fst _ (affineChart W) ≫ structureMap (W.baseChange S))
      (affineChart W ≫ structureMap W) _
    let H := (affineChart_isPullback W (algebraMap R S)).flip
    apply (affineCoefficientBase_isPullback (S := S) W).of_iso H.isoPullback
      (.refl _) (.refl _) (.refl _)
    · simp [WeierstrassCurve.baseChange]
    · simp [WeierstrassCurve.baseChange]
    · simp
    · simp

/-- The actual coefficient-base-change isomorphism, over the literal affine base. -/
def coefficientBaseChangeIso :
    scheme (W.baseChange S) ≅
      pullback (structureMap W) (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (coefficientBaseChange_isPullback (S := S) W).isoPullback

@[reassoc (attr := simp)] lemma coefficientBaseChangeIso_hom_fst :
    (coefficientBaseChangeIso (S := S) W).hom ≫ pullback.fst _ _ =
      coefficientSchemeMap W (algebraMap R S) :=
  (coefficientBaseChange_isPullback (S := S) W).isoPullback_hom_fst

@[reassoc (attr := simp)] lemma coefficientBaseChangeIso_hom_snd :
    (coefficientBaseChangeIso (S := S) W).hom ≫ pullback.snd _ _ =
      structureMap (W.baseChange S) :=
  (coefficientBaseChange_isPullback (S := S) W).isoPullback_hom_snd

/-- The forward isomorphism is the canonical lift of the two original morphisms. -/
lemma coefficientBaseChangeIso_hom :
    (coefficientBaseChangeIso (S := S) W).hom =
      pullback.lift (coefficientSchemeMap W (algebraMap R S))
        (structureMap (W.baseChange S)) (coefficientSchemeMap_structure W (algebraMap R S)) := by
  apply pullback.hom_ext <;> simp

omit [Algebra R S] in
/-- Coefficient change preserves the already constructed infinity-chart evaluation. -/
lemma infinityChartEval_coefficient (f : R →+* S) :
    (infinityChartEval (W.map f)).comp (chartCoefficientMap W f 1) =
      f.comp (infinityChartEval W) := by
  have h : ((infinityChartEval (W.map f)).comp (chartCoefficientMap W f 1)).comp
      (normalizePolynomial W 1) =
      (f.comp (infinityChartEval W)).comp (normalizePolynomial W 1) := by
    ext a
    · simp [normalizePolynomial]
    · fin_cases a <;> simp [normalizePolynomial]
  apply RingHom.ext
  intro a
  obtain ⟨p, rfl⟩ := normalizePolynomial_surjective W 1 a
  exact congrArg (fun g : MvPolynomial (Fin 3) R →+* S => g p) h

omit [Algebra R S] in
/-- The actual projective coefficient morphism preserves the literal infinity section. -/
@[reassoc] theorem infinitySection_coefficient (f : R →+* S) :
    infinitySection (W.map f) ≫ coefficientSchemeMap W f =
      Spec.map (CommRingCat.ofHom f) ≫ infinitySection W := by
  simp only [infinitySection]
  rw [Category.assoc, chartCoefficientMap_spec, ← Category.assoc, ← Spec.map_comp,
    ← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  exact infinityChartEval_coefficient W f

/-- Base change of the original infinity section into the literal categorical pullback. -/
def baseChangedInfinitySection : Spec (.of S) ⟶
    pullback (structureMap W) (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ infinitySection W)
    (𝟙 _) (by simp only [Category.assoc, infinitySection_structure, Category.comp_id,
      Category.id_comp])

/-- The coefficient-base-change isomorphism is pointed, with the literal section pullback. -/
@[reassoc] theorem coefficientBaseChangeIso_pointed :
    infinitySection (W.baseChange S) ≫ (coefficientBaseChangeIso (S := S) W).hom =
      baseChangedInfinitySection (S := S) W := by
  apply pullback.hom_ext
  · simp [baseChangedInfinitySection, WeierstrassCurve.baseChange, infinitySection_coefficient]
  · simp [baseChangedInfinitySection, infinitySection_structure]

end WeierstrassCurve.Projective

/- Migration source: PointedResolution.Weierstrass.BaseChange.
Frozen R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 260dc4c309e8710cdcfe22cb5c5e2003436d334a86f10272abd172b6b26bb69b. -/
