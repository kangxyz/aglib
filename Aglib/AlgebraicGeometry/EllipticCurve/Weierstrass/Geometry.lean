/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.SmoothLoci
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.Integrality
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.BaseChange
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.Genus
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.GeometryInputs
public import Aglib.AlgebraicGeometry.Curves.Basic
public import Aglib.AlgebraicGeometry.Geometrically.Integral.GlobalSections
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Geometry of the literal Weierstrass cubic

The existing two Jacobian localizations and the smooth infinity neighborhood
cover the original homogeneous-quotient Proj when the discriminant is nonzero.
Integrality holds after every coefficient field extension, including for singular
Weierstrass cubics. All morphisms are the original structural and chart maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeierstrassCurve.Projective

universe u
variable {k : Type u} [Field k]

/-- No prime of the actual affine ring contains both gradients of a nonsingular
Weierstrass equation. The quotient-domain argument works in every characteristic. -/
theorem affineJacobian_notMem_or (W : WeierstrassCurve k) (hΔ : W.Δ ≠ 0)
    (p : Ideal (affineRing W)) [p.IsPrime] :
    affineJacobian W 0 ∉ p ∨ affineJacobian W 1 ∉ p := by
  let q : affineRing W →+* affineRing W ⧸ p := Ideal.Quotient.mk p
  let f : k →+* affineRing W ⧸ p := q.comp (algebraMap k (affineRing W))
  have hΔ' : (W.map f).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ]
    exact fun h => hΔ (f.injective (by simpa using h))
  have he : (W.map f).toAffine.Equation (q (affineX W)) (q (affineY W)) := by
    rw [WeierstrassCurve.Affine.equation_iff']
    have h := congrArg q (affine_relation W)
    simp only [map_add, map_sub, map_mul, map_pow, map_zero] at h
    change q (affineY W) ^ 2 + f W.a₁ * q (affineX W) * q (affineY W) +
      f W.a₃ * q (affineY W) - (q (affineX W) ^ 3 +
        f W.a₂ * q (affineX W) ^ 2 + f W.a₄ * q (affineX W) + f W.a₆) = 0
    linear_combination h
  have hn := ((W.map f).toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ').mp he
  rw [WeierstrassCurve.Affine.nonsingular_iff'] at hn
  rcases hn.2 with hx | hy
  · left
    intro hp
    apply hx
    have h : q (affineJacobian W 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
    simpa only [affineJacobian_zero, f, map_add, map_sub, map_mul, map_pow, map_ofNat,
      RingHom.comp_apply, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₄] using h
  · right
    intro hp
    apply hy
    have h : q (affineJacobian W 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
    simpa only [affineJacobian_one, f, map_add, map_mul, map_ofNat,
      RingHom.comp_apply, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃] using h

/-- A three-chart smooth cover of the same projective cubic. -/
def nonsingularSmoothCover (W : WeierstrassCurve k) (hΔ : W.Δ ≠ 0) :
    (scheme W).OpenCover :=
  Scheme.Cover.mkOfCovers (Option (Fin 2))
    (fun | none => Spec (.of (infinitySmoothRing W))
         | some i => Spec (.of (affineSmoothRing W i)))
    (fun | none => infinitySmoothChart W | some i => affineSmoothChart W i)
    (by
      intro p
      rcases affine_or_smoothInfinity W p with hp | hp
      · obtain ⟨q, rfl⟩ := hp
        rcases affineJacobian_notMem_or W hΔ q.asIdeal with hx | hy
        · obtain ⟨r, hr⟩ := (affineChart_mem_smoothChart_iff W 0 q).mpr hx
          exact ⟨some 0, r, hr⟩
        · obtain ⟨r, hr⟩ := (affineChart_mem_smoothChart_iff W 1 q).mpr hy
          exact ⟨some 1, r, hr⟩
      · obtain ⟨q, hq⟩ := hp
        exact ⟨none, q, hq⟩)
    (by intro i; cases i <;> infer_instance)

/-- Smoothness of relative dimension one for the actual structural morphism,
uniformly over all fields and in characteristics two and three. -/
theorem structureMap_smoothOne (W : WeierstrassCurve k) (hΔ : W.Δ ≠ 0) :
    SmoothOfRelativeDimension 1 (structureMap W) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension 1)
    (nonsingularSmoothCover W hΔ)
  intro i
  cases i <;> first
  | exact infinitySmoothChart_smoothOne W
  | exact affineSmoothChart_smoothOne W _

/-- Every coefficient field extension of the literal cubic is integral, without
a discriminant hypothesis. The comparison is the original coefficient pullback. -/
theorem structureMap_geometricallyIntegral (W : WeierstrassCurve k) :
    GeometricallyIntegral (structureMap W) := by
  constructor
  intro K _ s Z fst snd hp
  let f : k →+* K := (Spec.preimage s).hom
  let : Algebra k K := f.toAlgebra
  have hs : Spec.map (CommRingCat.ofHom (algebraMap k K)) = s := by
    exact Spec.map_preimage s
  rw [← hs] at hp
  let : IsIntegral (scheme (W.baseChange K)) := scheme_isIntegral_of_isDomain _
  exact IsIntegral.of_isIso ((coefficientBaseChangeIso (S := K) W) ≪≫ hp.isoPullback.symm).hom

/-- Geometric connectedness of the original cubic, including singular equations. -/
theorem structureMap_geometricallyConnected (W : WeierstrassCurve k) :
    GeometricallyConnected (structureMap W) := by
  let := structureMap_geometricallyIntegral W
  constructor
  intro K _ s Z fst snd hp
  let : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral s fst snd hp
  infer_instance

/-- Native smooth proper geometrically connected curve properties of the same
homogeneous-quotient Proj. No geometry or cohomology supplier is assumed. -/
theorem curveOver_properties (W : WeierstrassCurve k) (hΔ : W.Δ ≠ 0) :
    Scheme.OverField.Curve.Properties (curveOver W) :=
  ⟨structureMap_smoothOne W hΔ, structureMap_proper W,
    structureMap_geometricallyConnected W⟩

/-- The original structural constants map is an isomorphism for every
Weierstrass cubic over a field, including singular cubics. -/
theorem curveOver_constants_bijective (W : WeierstrassCurve k) :
    Function.Bijective (Scheme.constants (curveOver W)) :=
  @Scheme.constants_bijective_of_proper_geometricallyIntegral k _ (curveOver W)
    (structureMap_proper W) (structureMap_geometricallyIntegral W)

end WeierstrassCurve.Projective

namespace WeierstrassCurve.Projective

universe u

/-- The original all-fields geometry family, on the same literal cubic and
with its original coherent genus. No additional supplier is assumed. -/
theorem nonsingularWeierstrassGeometry : NonsingularWeierstrassGeometry.{u} := by
  intro k _ W hΔ
  exact ⟨curveOver_properties W hΔ, curveOver_coherentGenus W⟩

end WeierstrassCurve.Projective
