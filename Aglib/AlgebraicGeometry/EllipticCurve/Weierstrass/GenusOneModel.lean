/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.Presentation
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.IntegralModel

/-!
# Minimal integral equations for original pointed genus-one curves

The original smooth proper geometrically connected field curve, its actual
rational section and coherent genus one supply the literal pointed Weierstrass
presentation. The native DVR minimum producer then gives an integral equation
with nonzero discriminant, preserving Mathlib's actual `IsMinimal` predicate.

The integral cubic is proper and flat over the original DVR. Its pointed generic
comparison is the actual presentation followed by the inverse of the original
native variable-change comparison. For the categorical generic pullback we keep
the existing coefficient-base-change interface's same-universe boundary.
No characteristic, perfectness, group-law or supplied-model hypothesis is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.OverField.Curve
open WeierstrassCurve.Projective

namespace WeierstrassCurve.GenusOneModel

universe u v

section CoefficientModel

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]

/-- An original pointed genus-one curve has an actual integral equation with
nonzero discriminant and the native valuation minimum. The generic coefficient
comparison preserves the original field, curve and section. The ring and field
universes remain independent in this equation-level statement. -/
theorem exists_minimal_pointed_equation (X : FScheme K) (hX : Properties X)
    (p : Spec (.of K) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus K X = 1) :
    ∃ V : WeierstrassCurve R, V.Δ ≠ 0 ∧
      WeierstrassCurve.IsMinimal R (V.map (algebraMap R K)) ∧
      AlgebraicGeometry.IsIntegral (scheme V) ∧
      IsProper (structureMap V) ∧ Flat (structureMap V) ∧
      ∃ E : X ≅ curveOver (V.map (algebraMap R K)),
        p ≫ E.hom.left = infinitySection (V.map (algebraMap R K)) := by
  obtain ⟨W, hW, E, hpoint⟩ :=
    WeierstrassCurve.Presentation.exists_nonsingular_pointed_weierstrassPresentation
      X hX p hp hg
  refine ⟨IntegralModel.minimalEquation R W,
    (IntegralModel.minimalEquation_discriminant_ne_zero_iff R W).mpr hW,
    inferInstance, scheme_isIntegral_of_isDomain _, inferInstance, inferInstance,
    E ≪≫ (IntegralModel.minimalGenericOverIso R W).symm, ?_⟩
  change p ≫ E.hom.left ≫ (IntegralModel.minimalGenericOverIso R W).inv.left = _
  rw [← Category.assoc, hpoint, ← IntegralModel.minimalGenericOverIso_infinity R W,
    Category.assoc]
  simp only [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  exact Category.comp_id _

end CoefficientModel

section CategoricalGenericFibre

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]

/-- An original pointed genus-one curve is the actual generic base change of a
proper flat integral Weierstrass equation with nonzero discriminant and native
valuation minimality. The comparison is over the original `Spec K` and sends
the original section to the literal pullback of integral infinity. This retains
the native categorical base-change interface's same-universe condition. -/
theorem exists_minimal_pointed_genericFibre (X : FScheme K) (hX : Properties X)
    (p : Spec (.of K) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus K X = 1) :
    ∃ V : WeierstrassCurve R, V.Δ ≠ 0 ∧
      WeierstrassCurve.IsMinimal R (V.map (algebraMap R K)) ∧
      AlgebraicGeometry.IsIntegral (scheme V) ∧
      IsProper (structureMap V) ∧ Flat (structureMap V) ∧
      ∃ E : X ≅ Over.mk (pullback.snd (structureMap V)
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
        p ≫ E.hom.left = baseChangedInfinitySection (S := K) V := by
  obtain ⟨V, hΔ, hmin, hintegral, hproper, hflat, E, hpoint⟩ :=
    exists_minimal_pointed_equation R X hX p hp hg
  refine ⟨V, hΔ, hmin, hintegral, hproper, hflat,
    E ≪≫ IntegralModel.coefficientBaseChangeOverIso R V, ?_⟩
  change p ≫ E.hom.left ≫ (coefficientBaseChangeIso (S := K) V).hom = _
  rw [← Category.assoc, hpoint]
  simpa only [WeierstrassCurve.baseChange] using
    coefficientBaseChangeIso_pointed (S := K) V

end CategoricalGenericFibre

end WeierstrassCurve.GenusOneModel
