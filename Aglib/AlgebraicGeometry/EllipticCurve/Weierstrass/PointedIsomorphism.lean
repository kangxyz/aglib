/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.GeometryInputs
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.PoleBasis
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.VariableChange
public import Aglib.AlgebraicGeometry.AffineScheme.IsomorphismCoordinates

/-!
# The affine pullback of an actual pointed projective isomorphism

The actual infinity complement identifies the restriction of an arbitrary
pointed isomorphism with an algebra isomorphism of the literal coordinate
rings. All fields and the original structural maps are retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Polynomial MonoidalCategory
open scoped Polynomial.Bivariate
open AlgebraicGeometry.Scheme.OverField
universe u

namespace WeierstrassCurve.Projective

attribute [local instance] Over.cartesianMonoidalCategory
variable {k : Type u} [Field k] {W V : WeierstrassCurve k}

/-- The inverse of the given pointed isomorphism preserves the same origin. -/
theorem pointedIso_inv (e : curveOver W ≅ curveOver V)
    (he : originOver W ≫ e.hom = originOver V) :
    originOver V ≫ e.inv = originOver W := by
  rw [← he, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- A pointed isomorphism carries the exact affine complement into itself. -/
theorem pointedIso_affine_range (e : curveOver W ≅ curveOver V)
    (he : originOver W ≫ e.hom = originOver V) :
    Set.range (affineChart W ≫ e.hom.left) ⊆ Set.range (affineChart V) := by
  have ho : e.hom.left (infinityPoint W) = infinityPoint V :=
    congrArg (fun p : 𝟙_ (FScheme k) ⟶ curveOver V =>
      p.left (IsLocalRing.closedPoint k)) he
  rintro _ ⟨p, rfl⟩
  rw [affineChart_range_complement]
  change e.hom.left (affineChart W p) ≠ infinityPoint V
  rw [← ho]
  intro hp
  have hpoint : affineChart W p = infinityPoint W :=
    e.hom.left.isOpenEmbedding.injective hp
  have hr : affineChart W p ∈ Set.range (affineChart W) := ⟨p, rfl⟩
  rw [affineChart_range_complement] at hr
  exact hr hpoint

/-- Restriction of the actual pointed projective isomorphism to its affine
complement, in the same covariant direction. -/
def pointedAffineMap (e : curveOver W ≅ curveOver V)
    (he : originOver W ≫ e.hom = originOver V) :
    (affineOver W).left ⟶ (affineOver V).left :=
  IsOpenImmersion.lift (affineChart V) (affineChart W ≫ e.hom.left)
    (pointedIso_affine_range e he)

@[reassoc] theorem pointedAffineMap_fac (e : curveOver W ≅ curveOver V)
    (he : originOver W ≫ e.hom = originOver V) :
    pointedAffineMap e he ≫ affineChart V = affineChart W ≫ e.hom.left :=
  IsOpenImmersion.lift_fac _ _ _

/-- The inverse arrow carries the target affine complement into the source complement. -/
theorem pointedIso_inverse_affine_range (e : curveOver W ≅ curveOver V)
    (he : originOver W ≫ e.hom = originOver V) :
    Set.range (affineChart V ≫ e.inv.left) ⊆ Set.range (affineChart W) := by
  have ho : e.inv.left (infinityPoint V) = infinityPoint W :=
    congrArg (fun p : 𝟙_ (FScheme k) ⟶ curveOver W =>
      p.left (IsLocalRing.closedPoint k)) (pointedIso_inv e he)
  rintro _ ⟨p, rfl⟩
  rw [affineChart_range_complement]
  change e.inv.left (affineChart V p) ≠ infinityPoint W
  rw [← ho]
  intro hp
  have hpoint : affineChart V p = infinityPoint V :=
    e.inv.left.isOpenEmbedding.injective hp
  have hr : affineChart V p ∈ Set.range (affineChart V) := ⟨p, rfl⟩
  rw [affineChart_range_complement] at hr
  exact hr hpoint

/-- Restriction of the original inverse arrow to the two affine complements. -/
def pointedAffineInverse (e : curveOver W ≅ curveOver V)
    (he : originOver W ≫ e.hom = originOver V) :
    (affineOver V).left ⟶ (affineOver W).left :=
  IsOpenImmersion.lift (affineChart W) (affineChart V ≫ e.inv.left)
    (pointedIso_inverse_affine_range e he)

@[reassoc] theorem pointedAffineInverse_fac (e : curveOver W ≅ curveOver V)
    (he : originOver W ≫ e.hom = originOver V) :
    pointedAffineInverse e he ≫ affineChart W = affineChart V ≫ e.inv.left :=
  IsOpenImmersion.lift_fac _ _ _

/-- The forward and inverse restrictions compose to the source identity. -/
theorem pointedAffineMap_comp_inverse (e : curveOver W ≅ curveOver V)
    (he : originOver W ≫ e.hom = originOver V) :
    pointedAffineMap e he ≫ pointedAffineInverse e he = 𝟙 (affineOver W).left := by
  have hF := pointedAffineMap_fac e he
  have hH := pointedAffineInverse_fac e he
  have hi : e.hom.left ≫ e.inv.left = 𝟙 (scheme W) :=
    congrArg Over.Hom.left e.hom_inv_id
  apply (cancel_mono (affineChart W)).mp
  rw [Category.assoc, hH, ← Category.assoc, hF, Category.assoc, hi]
  simp only [Category.comp_id, Category.id_comp]

/-- The inverse and forward restrictions compose to the target identity. -/
theorem pointedAffineInverse_comp_map (e : curveOver W ≅ curveOver V)
    (he : originOver W ≫ e.hom = originOver V) :
    pointedAffineInverse e he ≫ pointedAffineMap e he = 𝟙 (affineOver V).left := by
  have hF := pointedAffineMap_fac e he
  have hH := pointedAffineInverse_fac e he
  have hi : e.inv.left ≫ e.hom.left = 𝟙 (scheme V) :=
    congrArg Over.Hom.left e.inv_hom_id
  apply (cancel_mono (affineChart V)).mp
  rw [Category.assoc, hF, ← Category.assoc, hH, Category.assoc, hi]
  simp only [Category.comp_id, Category.id_comp]

/-- The restriction is an actual isomorphism of the original affine spectra. -/
def pointedAffineIso (e : curveOver W ≅ curveOver V)
    (he : originOver W ≫ e.hom = originOver V) :
    (affineOver W).left ≅ (affineOver V).left where
  hom := pointedAffineMap e he
  inv := pointedAffineInverse e he
  hom_inv_id := pointedAffineMap_comp_inverse e he
  inv_hom_id := pointedAffineInverse_comp_map e he

/-- Restriction preserves the literal base-field structural map. -/
theorem pointedAffineIso_over (e : curveOver W ≅ curveOver V)
    (he : originOver W ≫ e.hom = originOver V) :
    (pointedAffineIso e he).hom ≫ (affineOver V).hom = (affineOver W).hom := by
  change pointedAffineMap e he ≫ Spec.map (CommRingCat.ofHom (algebraMap k _)) = _
  rw [← affineChart_structure V, ← Category.assoc, pointedAffineMap_fac, Category.assoc]
  change affineChart W ≫ (e.hom.left ≫ (curveOver V).hom) = _
  rw [Over.w]
  exact affineChart_structure W

/-- The actual contravariant affine pullback of an arbitrary pointed
projective isomorphism. Its direction is the direction of the inverse
spectrum arrow, exactly as supplied by the fully faithful Spec functor. -/
def pointedAffineAlgEquiv (e : curveOver W ≅ curveOver V)
    (he : originOver W ≫ e.hom = originOver V) : affineRing W ≃ₐ[k] affineRing V :=
  AlgebraicGeometry.Spec.algEquivOfIso k (pointedAffineIso e he)
    (pointedAffineIso_over e he)

@[simp] theorem pointedAffineAlgEquiv_spec (e : curveOver W ≅ curveOver V)
    (he : originOver W ≫ e.hom = originOver V) :
    Spec.map (CommRingCat.ofHom (pointedAffineAlgEquiv e he : affineRing W →+* affineRing V)) =
      (pointedAffineIso e he).inv :=
  AlgebraicGeometry.Spec.map_algEquivOfIso k (pointedAffineIso e he)
    (pointedAffineIso_over e he)

/-- An arbitrary pointed projective isomorphism, without a characteristic
hypothesis, has triangular affine coordinate formulas. -/
theorem pointedAffineAlgEquiv_coordinateForms (e : curveOver W ≅ curveOver V)
    (he : originOver W ≫ e.hom = originOver V) :
    (∃ a r : k, pointedAffineAlgEquiv e he (affineX W) =
      algebraMap k _ a * affineX V + algebraMap k _ r) ∧
    (∃ b s t : k, pointedAffineAlgEquiv e he (affineY W) =
      algebraMap k _ b * affineY V + algebraMap k _ s * affineX V + algebraMap k _ t) :=
  affineAlgEquiv_coordinateForms W V (pointedAffineAlgEquiv e he)


private theorem affine_relation_unique (U V : WeierstrassCurve k)
    (hU : affineY V ^ 2 + algebraMap k _ U.a₁ * affineX V * affineY V +
      algebraMap k _ U.a₃ * affineY V -
      (affineX V ^ 3 + algebraMap k _ U.a₂ * affineX V ^ 2 +
        algebraMap k _ U.a₄ * affineX V + algebraMap k _ U.a₆) = 0) : U = V := by
  let p : k[X] := C (V.a₂ - U.a₂) * X ^ 2 + C (V.a₄ - U.a₄) * X + C (V.a₆ - U.a₆)
  let q : k[X] := C (U.a₁ - V.a₁) * X + C (U.a₃ - V.a₃)
  have hn : p • (1 : V.toAffine.CoordinateRing) + q • affineY V = 0 := by
    simp only [p, q, Algebra.smul_def, mul_one, map_add, map_sub, map_mul, map_pow,
      ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply k k[X]]
    linear_combination hU - affine_relation V
  obtain ⟨hp, hq⟩ := Affine.CoordinateRing.smul_basis_eq_zero hn
  have h1 : U.a₁ - V.a₁ = 0 := by
    have hc := congrArg (fun f : k[X] => f.coeff 1) hq
    simp only [q, coeff_add, coeff_C_mul_X, coeff_C, coeff_zero] at hc
    norm_num at hc
    exact hc
  have h2 : V.a₂ - U.a₂ = 0 := by
    have hc := congrArg (fun f : k[X] => f.coeff 2) hp
    simp only [p, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero] at hc
    norm_num at hc
    exact hc
  have h3 : U.a₃ - V.a₃ = 0 := by
    have hc := congrArg (fun f : k[X] => f.coeff 0) hq
    simp only [q, coeff_add, coeff_C_mul_X, coeff_C, coeff_zero] at hc
    norm_num at hc
    exact hc
  have h4 : V.a₄ - U.a₄ = 0 := by
    have hc := congrArg (fun f : k[X] => f.coeff 1) hp
    simp only [p, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero] at hc
    norm_num at hc
    exact hc
  have h6 : V.a₆ - U.a₆ = 0 := by
    have hc := congrArg (fun f : k[X] => f.coeff 0) hp
    simp only [p, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero] at hc
    norm_num at hc
    exact hc
  ext
  · exact sub_eq_zero.mp h1
  · exact (sub_eq_zero.mp h2).symm
  · exact sub_eq_zero.mp h3
  · exact (sub_eq_zero.mp h4).symm
  · exact (sub_eq_zero.mp h6).symm

private theorem affineAlgEquiv_leadingRelation (W V : WeierstrassCurve k)
    (e : W.toAffine.CoordinateRing ≃ₐ[k] V.toAffine.CoordinateRing)
    (a r b s t : k)
    (hx : e (affineX W) = algebraMap k _ a * affineX V + algebraMap k _ r)
    (hy : e (affineY W) = algebraMap k _ b * affineY V +
      algebraMap k _ s * affineX V + algebraMap k _ t) : b ^ 2 = a ^ 3 := by
  let p : k[X] := C (b ^ 2 - a ^ 3) * X ^ 3 +
    C (b ^ 2 * V.a₂ + s ^ 2 + W.a₁ * a * s - 3 * a ^ 2 * r - W.a₂ * a ^ 2) * X ^ 2 +
    C (b ^ 2 * V.a₄ + 2 * s * t + W.a₁ * (a * t + r * s) + W.a₃ * s -
      3 * a * r ^ 2 - 2 * W.a₂ * a * r - W.a₄ * a) * X +
    C (b ^ 2 * V.a₆ + t ^ 2 + W.a₁ * r * t + W.a₃ * t - r ^ 3 -
      W.a₂ * r ^ 2 - W.a₄ * r - W.a₆)
  let q : k[X] := C (-b ^ 2 * V.a₁ + 2 * b * s + W.a₁ * a * b) * X +
    C (-b ^ 2 * V.a₃ + 2 * b * t + W.a₁ * r * b + W.a₃ * b)
  have heq := congrArg e (affine_relation W)
  simp only [map_sub, map_add, map_mul, map_pow, e.commutes, map_zero, hx, hy] at heq
  have hn : p • (1 : V.toAffine.CoordinateRing) + q • affineY V = 0 := by
    simp only [p, q, Algebra.smul_def, mul_one, map_add, map_sub, map_mul, map_pow,
      map_neg, map_ofNat, ← Polynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply k k[X]]
    linear_combination heq - (algebraMap k V.toAffine.CoordinateRing b) ^ 2 * affine_relation V
  have hp := (Affine.CoordinateRing.smul_basis_eq_zero hn).1
  apply sub_eq_zero.mp
  have hc := congrArg (fun f : k[X] => f.coeff 3) hp
  simp only [p, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero] at hc
  norm_num at hc
  exact hc

private theorem affineX_ne_constant (W : WeierstrassCurve k) (r : k) :
    affineX W ≠ algebraMap k W.toAffine.CoordinateRing r := by
  intro h
  apply X_sub_C_ne_zero r
  apply FaithfulSMul.algebraMap_injective k[X] W.toAffine.CoordinateRing
  simpa only [map_sub, map_zero, sub_eq_zero, ← Polynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply k k[X]] using h

/-- Every actual algebra isomorphism between affine Weierstrass coordinate
rings gives an admissible variable change over the original field. No roots,
characteristic restriction, or classification premise is needed. -/
theorem affineAlgEquiv_exists_variableChange (W V : WeierstrassCurve k)
    (e : W.toAffine.CoordinateRing ≃ₐ[k] V.toAffine.CoordinateRing) :
    ∃ v : VariableChange k, v • W = V := by
  obtain ⟨⟨a, r, hx⟩, ⟨b, s, t, hy⟩⟩ := affineAlgEquiv_coordinateForms W V e
  have ha : a ≠ 0 := by
    intro ha
    have h := congrArg e.symm hx
    simp only [ha, map_zero, zero_mul, zero_add, e.symm_apply_apply, e.symm.commutes] at h
    exact affineX_ne_constant W r h
  have hab := affineAlgEquiv_leadingRelation W V e a r b s t hx hy
  have hb : b ≠ 0 := by
    intro hb
    exact pow_ne_zero 3 ha (by simpa [hb] using hab.symm)
  let u : kˣ := Units.mk0 (b / a) (div_ne_zero hb ha)
  have hu2 : (u : k) ^ 2 = a := by
    change (b / a) ^ 2 = a
    field_simp
    linear_combination hab
  have hu3 : (u : k) ^ 3 = b := by
    calc
      (u : k) ^ 3 = (u : k) * (u : k) ^ 2 := by ring
      _ = (b / a) * a := by rw [hu2]; rfl
      _ = b := div_mul_cancel₀ b ha
  let v : VariableChange k := ⟨u, r, s / a, t⟩
  refine ⟨v, ?_⟩
  have hx' : e (affineX W) = VariableChange.changeX
      (v.map (algebraMap k V.toAffine.CoordinateRing)) (affineX V) := by
    rw [hx]
    simp only [VariableChange.changeX, v, VariableChange.map,
      Units.coe_map, MonoidHom.coe_coe, ← map_pow, hu2]
  have hy' : e (affineY W) = VariableChange.changeY
      (v.map (algebraMap k V.toAffine.CoordinateRing)) (affineX V) (affineY V) := by
    rw [hy]
    simp only [VariableChange.changeY, v, VariableChange.map,
      Units.coe_map, MonoidHom.coe_coe, ← map_pow, hu2, hu3, ← map_mul,
      div_mul_cancel₀ s ha]
  have hmap : VariableChange.relation (W.map (algebraMap k V.toAffine.CoordinateRing))
      (e (affineX W)) (e (affineY W)) = 0 := by
    have heq := congrArg e (affine_relation W)
    simpa only [VariableChange.relation, Affine.evalEval_polynomial, map_sub, map_add,
      map_mul, map_pow, e.commutes, map_zero, WeierstrassCurve.map] using heq
  rw [hx', hy', VariableChange.relation_change, map_variableChange] at hmap
  have hu : ((v.map (algebraMap k V.toAffine.CoordinateRing)).u :
      V.toAffine.CoordinateRing) ^ 6 ≠ 0 := pow_ne_zero 6 (Units.ne_zero _)
  have hrel := (mul_eq_zero.mp hmap).resolve_left hu
  apply affine_relation_unique (v • W) V
  simpa only [VariableChange.relation, Affine.evalEval_polynomial, WeierstrassCurve.map] using hrel

/-- Classification is applied to the actual affine restriction of the given
pointed isomorphism. It is a conclusion, not a supplied bridge. -/
theorem pointedIso_exists_variableChange (e : curveOver W ≅ curveOver V)
    (he : originOver W ≫ e.hom = originOver V) :
    ∃ v : VariableChange k, v • W = V :=
  affineAlgEquiv_exists_variableChange W V (pointedAffineAlgEquiv e he)

/-- The original all-fields pointed-projective j-invariance family. -/
theorem pointedWeierstrassJInvariant : PointedWeierstrassJInvariant.{u} := by
  intro k _ W V hW hV e he
  obtain ⟨v, rfl⟩ := pointedIso_exists_variableChange e he
  let : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
  have h := variableChange_j W v
  simpa only [WeierstrassCurve.j_eq, div_eq_mul_inv, mul_comm] using h.symm

end WeierstrassCurve.Projective
