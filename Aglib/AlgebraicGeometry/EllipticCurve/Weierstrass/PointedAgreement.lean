/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.CofinitePoints
public import Aglib.AlgebraicGeometry.Group.PointedTranslation
public import Aglib.GroupTheory.Hom.Cofinite

/-!
# Cofinite point agreement forces a proper morphism to preserve the origin

Source: ordinary R5 Weierstrass.CofinitePoints, lines 200–313.
The actual original-base group objects, properness and geometric
integrality assumptions are explicit. The agreement is a pointwise premise.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField
namespace WeierstrassCurve.Projective
universe u
attribute [local instance] Over.cartesianMonoidalCategory
open AlgebraicGeometry.Scheme.Group.PointedMorphism
variable {k K : Type u} [Field k] [Field K]

/-- Actual scheme morphism pointedness from agreement with a group homomorphism
on a nonempty affine basic open. No global point formula, pointedness, field-map
algebraization, analytic pole-order result, or degree statement is assumed. -/
theorem extended_pointed_of_affineBasicOpen_agreement [IsAlgClosed K] [CharZero K]
    (W : WeierstrassCurve k) (f : k →+* K) (hΔ : W.Δ ≠ 0)
    [GrpObj (curveOver W)] (D : FScheme k) [GrpObj D]
    [IsProper (curveOver W).hom] [IsProper D.hom]
    [GeometricallyIntegral (curveOver W).hom]
    (m : curveOver W ⟶ D)
    (P : (extensionPointSource f ⟶ curveOver W) →* (extensionPointSource f ⟶ D))
    (d : affineRing W) (hd : d ≠ 0)
    (hgood : ∀ x y (hxy : (W.map f).toAffine.Nonsingular x y),
      affinePointEvalExtension W f x y hxy.1 d ≠ 0 →
      (coordinatePointExtension W f (.some x y hxy)) ≫ m =
        P (coordinatePointExtension W f (.some x y hxy))) :
    (toUnit (extensionPointSource f) ≫ η[curveOver W] ≫ m = 1) ∧
      ∀ x : extensionPointSource f ⟶ curveOver W, x ≫ m = P x := by
  let := infinite_extension_scheme_points W f hΔ
  let := pointedTranslate_isMonHom m
  let G := IsMonHom.monoidHom (pointedTranslate m) (extensionPointSource f)
  let c : extensionPointSource f ⟶ D := toUnit (extensionPointSource f) ≫ η[curveOver W] ≫ m
  have hGP : c = 1 ∧ G = P := by
    apply MonoidHom.translated_hom_eq_of_cofinite c G P (affineBasicOpenSchemePoints W f hΔ d)
      (affineBasicOpenSchemePoints_finite_compl W f hΔ d hd)
    intro x hx
    have hdecomp : c * G x = x ≫ m := by
      change c * (x ≫ pointedTranslate m) = _
      rw [pointedTranslate_point_formula]
      exact mul_inv_cancel_left _ _
    rw [hdecomp]
    obtain ⟨Q, rfl⟩ := (coordinateExtensionEquiv W f hΔ).surjective x
    have hQ : Q ∈ affineBasicOpenPoints W f d := by
      simpa [affineBasicOpenSchemePoints] using hx
    cases Q with
    | zero => exact False.elim hQ
    | some x y h => exact hgood x y h hQ
  refine ⟨hGP.1, fun x => ?_⟩
  have he := pointedTranslate_point_formula m x
  change G x = c⁻¹ * (x ≫ m) at he
  rw [hGP.1, inv_one, _root_.one_mul, hGP.2] at he
  exact he.symm

/-- Cofinite agreement determines the original scheme morphism at
all geometric points and forces its original base-field origin to be preserved. -/
theorem pointed_of_affineBasicOpen_agreement [IsAlgClosed K] [CharZero K]
    (W : WeierstrassCurve k) (f : k →+* K) (hΔ : W.Δ ≠ 0)
    [GrpObj (curveOver W)] (D : FScheme k) [GrpObj D]
    [IsProper (curveOver W).hom] [IsProper D.hom]
    [GeometricallyIntegral (curveOver W).hom]
    (m : curveOver W ⟶ D)
    (P : (extensionPointSource f ⟶ curveOver W) →* (extensionPointSource f ⟶ D))
    (d : affineRing W) (hd : d ≠ 0)
    (hgood : ∀ x y (hxy : (W.map f).toAffine.Nonsingular x y),
      affinePointEvalExtension W f x y hxy.1 d ≠ 0 →
      (coordinatePointExtension W f (.some x y hxy)) ≫ m =
        P (coordinatePointExtension W f (.some x y hxy))) :
    (η[curveOver W] ≫ m = η[D]) ∧
      ∀ x : extensionPointSource f ⟶ curveOver W, x ≫ m = P x := by
  obtain ⟨ho, hx⟩ := extended_pointed_of_affineBasicOpen_agreement W f hΔ D m P d hd hgood
  exact ⟨pointed_of_extended_pointed f m ho, hx⟩

theorem extended_pointed_of_affineBasicOpen_agreement_off_kernel [IsAlgClosed K] [CharZero K]
    (W : WeierstrassCurve k) (f : k →+* K) (hΔ : W.Δ ≠ 0)
    [GrpObj (curveOver W)] (D : FScheme k) [GrpObj D]
    [IsProper (curveOver W).hom] [IsProper D.hom]
    [GeometricallyIntegral (curveOver W).hom]
    (m : curveOver W ⟶ D)
    (P : (extensionPointSource f ⟶ curveOver W) →* (extensionPointSource f ⟶ D))
    [Finite P.ker]
    (d : affineRing W) (hd : d ≠ 0)
    (hgood : ∀ x y (hxy : (W.map f).toAffine.Nonsingular x y),
      affinePointEvalExtension W f x y hxy.1 d ≠ 0 →
      P (coordinatePointExtension W f (.some x y hxy)) ≠ 1 →
      (coordinatePointExtension W f (.some x y hxy)) ≫ m =
        P (coordinatePointExtension W f (.some x y hxy))) :
    (toUnit (extensionPointSource f) ≫ η[curveOver W] ≫ m = 1) ∧
      ∀ x : extensionPointSource f ⟶ curveOver W, x ≫ m = P x := by
  let := infinite_extension_scheme_points W f hΔ
  let := pointedTranslate_isMonHom m
  let G := IsMonHom.monoidHom (pointedTranslate m) (extensionPointSource f)
  let c : extensionPointSource f ⟶ D := toUnit (extensionPointSource f) ≫ η[curveOver W] ≫ m
  have hGP : c = 1 ∧ G = P := by
    apply MonoidHom.translated_hom_eq_of_cofinite c G P
      (affineBasicOpenSchemePoints W f hΔ d \ (P.ker : Set _))
    · simpa only [Set.compl_sdiff, Set.union_comm] using
        (affineBasicOpenSchemePoints_finite_compl W f hΔ d hd).union
          (Set.toFinite (P.ker : Set _))
    · intro x hx
      have hdecomp : c * G x = x ≫ m := by
        change c * (x ≫ pointedTranslate m) = _
        rw [pointedTranslate_point_formula]
        exact mul_inv_cancel_left _ _
      rw [hdecomp]
      obtain ⟨Q, rfl⟩ := (coordinateExtensionEquiv W f hΔ).surjective x
      have hQ : Q ∈ affineBasicOpenPoints W f d := by
        simpa [affineBasicOpenSchemePoints] using hx.1
      cases Q with
      | zero => exact False.elim hQ
      | some x y h => exact hgood x y h hQ hx.2
  refine ⟨hGP.1, fun x => ?_⟩
  have he := pointedTranslate_point_formula m x
  change G x = c⁻¹ * (x ≫ m) at he
  rw [hGP.1, inv_one, _root_.one_mul, hGP.2] at he
  exact he.symm


theorem pointed_of_affineBasicOpen_agreement_off_kernel [IsAlgClosed K] [CharZero K]
    (W : WeierstrassCurve k) (f : k →+* K) (hΔ : W.Δ ≠ 0)
    [GrpObj (curveOver W)] (D : FScheme k) [GrpObj D]
    [IsProper (curveOver W).hom] [IsProper D.hom]
    [GeometricallyIntegral (curveOver W).hom]
    (m : curveOver W ⟶ D)
    (P : (extensionPointSource f ⟶ curveOver W) →* (extensionPointSource f ⟶ D))
    [Finite P.ker]
    (d : affineRing W) (hd : d ≠ 0)
    (hgood : ∀ x y (hxy : (W.map f).toAffine.Nonsingular x y),
      affinePointEvalExtension W f x y hxy.1 d ≠ 0 →
      P (coordinatePointExtension W f (.some x y hxy)) ≠ 1 →
      (coordinatePointExtension W f (.some x y hxy)) ≫ m =
        P (coordinatePointExtension W f (.some x y hxy))) :
    (η[curveOver W] ≫ m = η[D]) ∧
      ∀ x : extensionPointSource f ⟶ curveOver W, x ≫ m = P x := by
  obtain ⟨ho, hx⟩ :=
    extended_pointed_of_affineBasicOpen_agreement_off_kernel W f hΔ D m P d hd hgood
  exact ⟨pointed_of_extended_pointed f m ho, hx⟩



end WeierstrassCurve.Projective
