/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Affine.Coordinates
public import Aglib.RingTheory.PlaneNode.Basic
public import Aglib.RingTheory.Etale.NonmonicPair
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Tangent extensions and plane-node coordinates

The tangent parameter produces explicit isomorphic extensions of the literal
Weierstrass affine coordinate ring and the plane-node ring. Inverting the two
derivative factors gives the same étale chart. The point maps work over any
coefficient homomorphism to a field; local residue maps are the specialization.
-/

@[expose] public noncomputable section

open Polynomial
open scoped Polynomial
universe u

open WeierstrassCurve

namespace WeierstrassCurve.Affine.TangentNode

variable {R : Type u} [CommRing R]

/-- Adjoin the tangent parameter with P(T)=X to the actual affine equation. -/
def tangentPoly (W : WeierstrassCurve R) : (W.toAffine.CoordinateRing)[X] :=
  X ^ 2 + C (algebraMap R _ W.a₁) * X - C (algebraMap R _ W.a₂) - C (affineX W)
/-- The affine Weierstrass coordinate ring with a root of the tangent polynomial adjoined. -/
abbrev TangentRing (W : WeierstrassCurve R) := AdjoinRoot (tangentPoly W)
/-- The adjoined tangent parameter in the affine tangent extension. -/
abbrev tangentT (W : WeierstrassCurve R) : TangentRing W := AdjoinRoot.root (tangentPoly W)
/-- The affine `x` coordinate in the tangent extension. -/
abbrev tangentX (W : WeierstrassCurve R) : TangentRing W := algebraMap (W.toAffine.CoordinateRing)
  _ (affineX W)
/-- The affine `y` coordinate in the tangent extension. -/
abbrev tangentY (W : WeierstrassCurve R) : TangentRing W := algebraMap (W.toAffine.CoordinateRing)
  _ (affineY W)

/-- The polynomial `(2T + a₁)(T² + a₁T - a₂) + U - V` over the plane-node ring. -/
def nodeTangentPoly (W : WeierstrassCurve R) : (PlaneNode.Ring W.a₆)[X] :=
  (2 * X + C (algebraMap R _ W.a₁)) *
    (X ^ 2 + C (algebraMap R _ W.a₁) * X - C (algebraMap R _ W.a₂)) +
    C (PlaneNode.U W.a₆) - C (PlaneNode.V W.a₆)
/-- The plane-node ring with a root of `nodeTangentPoly` adjoined. -/
abbrev NodeTangentRing (W : WeierstrassCurve R) := AdjoinRoot (nodeTangentPoly W)
/-- The adjoined parameter in the plane-node tangent extension. -/
abbrev nodeTangentT (W : WeierstrassCurve R) : NodeTangentRing W := AdjoinRoot.root
  (nodeTangentPoly W)
/-- The plane-node coordinate `U` in the tangent extension. -/
abbrev nodeTangentU (W : WeierstrassCurve R) : NodeTangentRing W := algebraMap (PlaneNode.Ring
  W.a₆) _ (PlaneNode.U W.a₆)
/-- The plane-node coordinate `V` in the tangent extension. -/
abbrev nodeTangentV (W : WeierstrassCurve R) : NodeTangentRing W := algebraMap (PlaneNode.Ring
  W.a₆) _ (PlaneNode.V W.a₆)
/-- The reconstructed Weierstrass coordinate `x = T² + a₁T - a₂` in the node tangent extension. -/
abbrev nodeTangentX (W : WeierstrassCurve R) : NodeTangentRing W :=
  nodeTangentT W ^ 2 + algebraMap R _ W.a₁ * nodeTangentT W - algebraMap R _ W.a₂
/-- The reconstructed Weierstrass coordinate `y = U + Tx` in the node tangent extension. -/
abbrev nodeTangentY (W : WeierstrassCurve R) : NodeTangentRing W :=
  nodeTangentU W + nodeTangentT W * nodeTangentX W

lemma tangent_relation (W : WeierstrassCurve R) :
    tangentT W ^ 2 + algebraMap R _ W.a₁ * tangentT W - algebraMap R _ W.a₂ = tangentX W := by
  have h := AdjoinRoot.eval₂_root (tangentPoly W)
  change (X ^ 2 + C (algebraMap R (W.toAffine.CoordinateRing) W.a₁) * X -
    C (algebraMap R (W.toAffine.CoordinateRing) W.a₂) - C (affineX W)).eval₂
      (algebraMap (W.toAffine.CoordinateRing) (TangentRing W)) (tangentT W) = 0 at h
  simp only [ eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C] at h
  simpa only [← AdjoinRoot.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply R (W.toAffine.CoordinateRing), sub_eq_zero] using h

lemma nodeTangent_relation (W : WeierstrassCurve R) :
    (2 * nodeTangentT W + algebraMap R _ W.a₁) * nodeTangentX W +
      nodeTangentU W - nodeTangentV W = 0 := by
  have h := AdjoinRoot.eval₂_root (nodeTangentPoly W)
  change ((2 * X + C (algebraMap R (PlaneNode.Ring W.a₆) W.a₁)) *
    (X ^ 2 + C (algebraMap R (PlaneNode.Ring W.a₆) W.a₁) * X - C (algebraMap R (PlaneNode.Ring
      W.a₆) W.a₂)) +
    C (PlaneNode.U W.a₆) - C (PlaneNode.V W.a₆)).eval₂
      (algebraMap (PlaneNode.Ring W.a₆) (NodeTangentRing W)) (nodeTangentT W) = 0 at h
  simp only [ eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_ofNat] at h
  simpa only [← AdjoinRoot.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply R (PlaneNode.Ring W.a₆)] using h

lemma nodeTangent_node_relation (W : WeierstrassCurve R) :
    nodeTangentU W * nodeTangentV W = algebraMap R _ W.a₆ := by
  have h := congrArg (algebraMap (PlaneNode.Ring W.a₆) (NodeTangentRing W)) (PlaneNode.relation
    W.a₆)
  simpa only [map_mul, ← IsScalarTower.algebraMap_apply R (PlaneNode.Ring W.a₆)] using h
lemma tangent_affine_relation (W : WeierstrassCurve R) (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) :
    tangentY W ^ 2 + algebraMap R _ W.a₁ * tangentX W * tangentY W -
      (tangentX W ^ 3 + algebraMap R _ W.a₂ * tangentX W ^ 2 + algebraMap R _ W.a₆) = 0 := by
  have h := congrArg (algebraMap (W.toAffine.CoordinateRing) (TangentRing W)) (affine_relation W)
  simpa only [h3, h4, map_zero, zero_mul, add_zero, map_sub, map_add, map_mul, map_pow,
    ← IsScalarTower.algebraMap_apply R (W.toAffine.CoordinateRing)] using h


lemma tangent_factor_relation (W : WeierstrassCurve R) (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) :
    (tangentY W - tangentT W * tangentX W) *
      (tangentY W + (algebraMap R _ W.a₁ + tangentT W) * tangentX W) =
    algebraMap R _ W.a₆ := by
  have hp := tangent_relation W
  have hw := tangent_affine_relation W h3 h4
  linear_combination hw - tangentX W ^ 2 * hp

/-- The actual node ring maps to the tangent extension by the two factor coordinates. -/
def nodeToTangent (W : WeierstrassCurve R) (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) :
    PlaneNode.Ring W.a₆ →ₐ[R] TangentRing W :=
  PlaneNode.lift W.a₆ (tangentY W - tangentT W * tangentX W)
    (tangentY W + (algebraMap R _ W.a₁ + tangentT W) * tangentX W)
    (tangent_factor_relation W h3 h4)

lemma nodeTangent_affine_relation (W : WeierstrassCurve R)
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) :
    nodeTangentY W ^ 2 + algebraMap R _ W.a₁ * nodeTangentX W * nodeTangentY W +
      algebraMap R _ W.a₃ * nodeTangentY W -
    (nodeTangentX W ^ 3 + algebraMap R _ W.a₂ * nodeTangentX W ^ 2 +
      algebraMap R _ W.a₄ * nodeTangentX W + algebraMap R _ W.a₆) = 0 := by
  have hq := nodeTangent_relation W
  have hn := nodeTangent_node_relation W
  simp only [h3, h4, map_zero, zero_mul, add_zero]
  dsimp [nodeTangentY, nodeTangentX] at *
  linear_combination hn + nodeTangentU W * hq

/-- The original affine equation maps to the node presentation by X=P(T), Y=U+TP(T). -/
def affineToNodeTangent (W : WeierstrassCurve R) (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) :
    W.toAffine.CoordinateRing →ₐ[R] NodeTangentRing W :=
  affineLift W (nodeTangentX W) (nodeTangentY W) (nodeTangent_affine_relation W h3 h4)

/-- The map from the affine tangent extension to the node tangent extension when `a₃ = a₄ = 0`. -/
def tangentToNodeTangent (W : WeierstrassCurve R) (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) :
    TangentRing W →ₐ[R] NodeTangentRing W :=
  AdjoinRoot.liftAlgHom (tangentPoly W) (affineToNodeTangent W h3 h4)
    (nodeTangentT W) (by
      simp only [tangentPoly, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X,
        eval₂_C, AlgHom.coe_toRingHom, AlgHom.commutes]
      simp only [affineToNodeTangent, affineLift_x, nodeTangentX, sub_self])

/-- The inverse-direction map from the node tangent extension when `a₃ = a₄ = 0`. -/
def nodeTangentToTangent (W : WeierstrassCurve R) (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) :
    NodeTangentRing W →ₐ[R] TangentRing W :=
  AdjoinRoot.liftAlgHom (nodeTangentPoly W) (nodeToTangent W h3 h4)
    (tangentT W) (by
      simp only [nodeTangentPoly, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X,
        eval₂_C, eval₂_ofNat, AlgHom.coe_toRingHom, AlgHom.commutes]
      simp only [nodeToTangent, PlaneNode.lift_U, PlaneNode.lift_V, tangent_relation]
      ring)

@[simp] lemma tangentToNodeTangent_t (W : WeierstrassCurve R) (h3) (h4) :
    tangentToNodeTangent W h3 h4 (tangentT W) = nodeTangentT W := by
  simp [tangentToNodeTangent, tangentT]
@[simp] lemma tangentToNodeTangent_x (W : WeierstrassCurve R) (h3) (h4) :
    tangentToNodeTangent W h3 h4 (tangentX W) = nodeTangentX W := by
  simp [tangentToNodeTangent, tangentX, AdjoinRoot.algebraMap_eq, affineToNodeTangent]
@[simp] lemma tangentToNodeTangent_y (W : WeierstrassCurve R) (h3) (h4) :
    tangentToNodeTangent W h3 h4 (tangentY W) = nodeTangentY W := by
  simp [tangentToNodeTangent, tangentY, AdjoinRoot.algebraMap_eq, affineToNodeTangent]
@[simp] lemma nodeTangentToTangent_t (W : WeierstrassCurve R) (h3) (h4) :
    nodeTangentToTangent W h3 h4 (nodeTangentT W) = tangentT W := by
  simp [nodeTangentToTangent, nodeTangentT]
@[simp] lemma nodeTangentToTangent_u (W : WeierstrassCurve R) (h3) (h4) :
    nodeTangentToTangent W h3 h4 (nodeTangentU W) = tangentY W - tangentT W * tangentX W := by
  simp [nodeTangentToTangent, nodeTangentU, AdjoinRoot.algebraMap_eq, nodeToTangent]
@[simp] lemma nodeTangentToTangent_v (W : WeierstrassCurve R) (h3) (h4) :
    nodeTangentToTangent W h3 h4 (nodeTangentV W) =
      tangentY W + (algebraMap R _ W.a₁ + tangentT W) * tangentX W := by
  simp [nodeTangentToTangent, nodeTangentV, AdjoinRoot.algebraMap_eq, nodeToTangent]

/-- An isomorphism of the two actual ring presentations, before localization. -/
def tangentEquiv (W : WeierstrassCurve R) (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) :
    TangentRing W ≃ₐ[R] NodeTangentRing W :=
  AlgEquiv.ofAlgHom (tangentToNodeTangent W h3 h4) (nodeTangentToTangent W h3 h4)
    (by
      apply AdjoinRoot.algHom_ext'
      · apply PlaneNode.hom_ext
        · simp only [AlgHom.comp_apply, AlgHom.id_apply, AdjoinRoot.ofAlgHom,
            AdjoinRoot.coe_ofAlgHom, ← AdjoinRoot.algebraMap_eq]
          change tangentToNodeTangent W h3 h4 (nodeTangentToTangent W h3 h4 (nodeTangentU W)) = _
          simp only [nodeTangentToTangent_u, map_sub, map_mul, tangentToNodeTangent_y,
            tangentToNodeTangent_t, tangentToNodeTangent_x, nodeTangentY, add_sub_cancel_right]
        · simp only [AlgHom.comp_apply, AlgHom.id_apply, AdjoinRoot.coe_ofAlgHom,
            ← AdjoinRoot.algebraMap_eq]
          change tangentToNodeTangent W h3 h4 (nodeTangentToTangent W h3 h4 (nodeTangentV W)) = _
          simp only [nodeTangentToTangent_v, map_add, map_mul, AlgHom.commutes,
            tangentToNodeTangent_y, tangentToNodeTangent_t, tangentToNodeTangent_x]
          have h := nodeTangent_relation W
          change nodeTangentY W + (algebraMap R _ W.a₁ + nodeTangentT W) * nodeTangentX W =
            nodeTangentV W
          dsimp [nodeTangentY]
          linear_combination h
      · simp)
    (by
      apply AdjoinRoot.algHom_ext'
      · apply affine_ext
        · simp only [AlgHom.comp_apply, AlgHom.id_apply, AdjoinRoot.coe_ofAlgHom,
            ← AdjoinRoot.algebraMap_eq]
          change nodeTangentToTangent W h3 h4 (tangentToNodeTangent W h3 h4 (tangentX W)) = _
          simp only [tangentToNodeTangent_x, nodeTangentX, map_sub, map_add, map_mul,
            map_pow, AlgHom.commutes, nodeTangentToTangent_t, tangent_relation]
        · simp only [AlgHom.comp_apply, AlgHom.id_apply, AdjoinRoot.coe_ofAlgHom,
            ← AdjoinRoot.algebraMap_eq]
          change nodeTangentToTangent W h3 h4 (tangentToNodeTangent W h3 h4 (tangentY W)) = _
          simp only [tangentToNodeTangent_y, nodeTangentY, nodeTangentX, map_sub, map_add,
            map_mul, map_pow, AlgHom.commutes, nodeTangentToTangent_u,
            nodeTangentToTangent_t, tangent_relation, sub_add_cancel]
      · simp)
/-- The derivative `2T + a` of the quadratic tangent expression. -/
def dOne (a : R) : R[X] := 2 * X + C a
/-- The derivative `6(T² + aT - b) + a² + 4b` of `(2T + a)(T² + aT - b)`. -/
def dTwo (a b : R) : R[X] := 6 * (X ^ 2 + C a * X - C b) + C (a ^ 2 + 4 * b)
lemma tangent_derivative (W : WeierstrassCurve R) :
    (tangentPoly W).derivative = dOne (algebraMap R _ W.a₁) := by
  simp [tangentPoly, dOne, derivative_pow, map_ofNat]
lemma nodeTangent_derivative (W : WeierstrassCurve R) :
    (nodeTangentPoly W).derivative = dTwo (algebraMap R _ W.a₁) (algebraMap R _ W.a₂) := by
  simp only [nodeTangentPoly, dTwo, derivative_sub, derivative_mul,
    derivative_pow, derivative_C, derivative_X, derivative_ofNat, zero_mul,
    mul_one, Nat.cast_ofNat, map_add, map_pow, map_mul, map_ofNat]
  ring

/-- The nonmonic etale presentation of the affine tangent extension, inverting both derivative
factors. -/
def tangentPair (W : WeierstrassCurve R) : NonmonicEtalePair (W.toAffine.CoordinateRing) where
  f := tangentPoly W
  g := dOne (algebraMap R _ W.a₁) * dTwo (algebraMap R _ W.a₁) (algebraMap R _ W.a₂)
  cond := ⟨dTwo (algebraMap R _ W.a₁) (algebraMap R _ W.a₂), 0, 1, by
    rw [tangent_derivative]; simp⟩
/-- The nonmonic etale presentation of the node tangent extension, inverting both derivative
factors. -/
def nodePair (W : WeierstrassCurve R) : NonmonicEtalePair (PlaneNode.Ring W.a₆) where
  f := nodeTangentPoly W
  g := dOne (algebraMap R _ W.a₁) * dTwo (algebraMap R _ W.a₁) (algebraMap R _ W.a₂)
  cond := ⟨dOne (algebraMap R _ W.a₁), 0, 1, by
    rw [nodeTangent_derivative]; simp [mul_comm]⟩

/-- The product of the two derivative factors in the affine tangent extension. -/
def tangentDenom (W : WeierstrassCurve R) : TangentRing W :=
  AdjoinRoot.mk (tangentPoly W) (tangentPair W).g
/-- The product of the two derivative factors in the node tangent extension. -/
def nodeDenom (W : WeierstrassCurve R) : NodeTangentRing W :=
  AdjoinRoot.mk (nodeTangentPoly W) (nodePair W).g
/-- The affine tangent extension localized by the product of the two derivative factors. -/
abbrev TangentChart (W : WeierstrassCurve R) := Localization.Away (tangentDenom W)
/-- The node tangent extension localized by the product of the two derivative factors. -/
abbrev NodeChart (W : WeierstrassCurve R) := Localization.Away (nodeDenom W)

/-- Both derivative factors are inverted. This includes every residue characteristic. -/
instance tangentChart_etale (W : WeierstrassCurve R) : Algebra.Etale (W.toAffine.CoordinateRing)
  (TangentChart W) :=
  Algebra.Etale.of_equiv (tangentPair W).equivAwayAdjoinRoot
/-- The localized node tangent chart is etale over the plane-node ring. -/
instance nodeChart_etale (W : WeierstrassCurve R) : Algebra.Etale (PlaneNode.Ring W.a₆) (NodeChart
  W) :=
  Algebra.Etale.of_equiv (nodePair W).equivAwayAdjoinRoot

lemma tangentDenom_eq (W : WeierstrassCurve R) :
    tangentDenom W = (2 * tangentT W + algebraMap R _ W.a₁) *
      (6 * (tangentT W ^ 2 + algebraMap R _ W.a₁ * tangentT W - algebraMap R _ W.a₂) +
        (algebraMap R _ W.a₁ ^ 2 + 4 * algebraMap R _ W.a₂)) := by
  change AdjoinRoot.mk (tangentPoly W)
    (dOne (algebraMap R _ W.a₁) * dTwo (algebraMap R _ W.a₁) (algebraMap R _ W.a₂)) = _
  simp only [dOne, dTwo, map_sub, map_add, map_mul, map_pow, map_ofNat, AdjoinRoot.mk_X,
    AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply R
      (W.toAffine.CoordinateRing)]
lemma nodeDenom_eq (W : WeierstrassCurve R) :
    nodeDenom W = (2 * nodeTangentT W + algebraMap R _ W.a₁) *
      (6 * (nodeTangentT W ^ 2 + algebraMap R _ W.a₁ * nodeTangentT W - algebraMap R _ W.a₂) +
        (algebraMap R _ W.a₁ ^ 2 + 4 * algebraMap R _ W.a₂)) := by
  change AdjoinRoot.mk (nodeTangentPoly W)
    (dOne (algebraMap R _ W.a₁) * dTwo (algebraMap R _ W.a₁) (algebraMap R _ W.a₂)) = _
  simp only [dOne, dTwo, map_sub, map_add, map_mul, map_pow, map_ofNat, AdjoinRoot.mk_X,
    AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply R
      (PlaneNode.Ring W.a₆)]
lemma tangentEquiv_denom (W : WeierstrassCurve R) (h3) (h4) :
    tangentEquiv W h3 h4 (tangentDenom W) = nodeDenom W := by
  rw [tangentDenom_eq, nodeDenom_eq]
  simp only [map_add, map_mul, map_sub, map_pow, map_ofNat, AlgEquiv.commutes]
  have ht : tangentEquiv W h3 h4 (tangentT W) = nodeTangentT W := tangentToNodeTangent_t W h3 h4
  rw [ht]

/-- The same actual common open chart in the two equation presentations. -/
def chartEquiv (W : WeierstrassCurve R) (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) :
    TangentChart W ≃ₐ[R] NodeChart W :=
  IsLocalization.algEquivOfAlgEquiv (M := Submonoid.powers (tangentDenom W))
    (T := Submonoid.powers (nodeDenom W)) (TangentChart W) (NodeChart W) (tangentEquiv W h3 h4)
    (by simp only [Submonoid.map_powers, tangentEquiv_denom])

lemma chartEquiv_on_tangent (W : WeierstrassCurve R) (h3) (h4) (x : TangentRing W) :
    chartEquiv W h3 h4 (algebraMap (TangentRing W) (TangentChart W) x) =
      algebraMap (NodeTangentRing W) (NodeChart W) (tangentEquiv W h3 h4 x) :=
  IsLocalization.algEquivOfAlgEquiv_eq _ x
section FieldPoint
variable {K : Type u} [Field K] [Algebra R K]
variable (W : WeierstrassCurve R) (h6 : algebraMap R K W.a₆ = 0)

/-- Evaluation at the affine origin over `K`, using the supplied vanishing of the image of `a₆`. -/
def affineOrigin : W.toAffine.CoordinateRing →ₐ[R] K :=
  affineLift W 0 0 (by simp [h6])
/-- Evaluation at the plane-node origin over `K`, using the supplied vanishing of the image of
`a₆`. -/
def nodeOrigin : PlaneNode.Ring W.a₆ →ₐ[R] K :=
  PlaneNode.lift W.a₆ 0 0 (by simp [h6])

variable (r : K)
variable (hr : r ^ 2 + algebraMap R K W.a₁ * r - algebraMap R K W.a₂ = 0)

/-- Evaluation of the affine tangent extension at the origin and the supplied tangent root `r`. -/
def tangentResidue : TangentRing W →ₐ[R] K :=
  AdjoinRoot.liftAlgHom (tangentPoly W) (affineOrigin W h6) r (by
    simp only [tangentPoly, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X,
      eval₂_C, AlgHom.coe_toRingHom, AlgHom.commutes]
    simp only [affineOrigin, affineLift_x, sub_zero, hr])

@[simp] lemma tangentResidue_t : tangentResidue W h6 r hr (tangentT W) = r := by
  simp [tangentResidue, tangentT]
@[simp] lemma tangentResidue_x : tangentResidue W h6 r hr (tangentX W) = 0 := by
  simp [tangentResidue, tangentX, AdjoinRoot.algebraMap_eq, affineOrigin]
@[simp] lemma tangentResidue_y : tangentResidue W h6 r hr (tangentY W) = 0 := by
  simp [tangentResidue, tangentY, AdjoinRoot.algebraMap_eq, affineOrigin]

lemma tangentResidue_denom :
    tangentResidue W h6 r hr (tangentDenom W) = (2 * r + algebraMap R K W.a₁) ^ 3 := by
  rw [tangentDenom_eq]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, AlgHom.commutes,
    tangentResidue_t, hr, mul_zero, zero_add]
  linear_combination -(4 * (2 * r + algebraMap R K W.a₁)) * hr

variable (hs : 2 * r + algebraMap R K W.a₁ ≠ 0)

/-- The actual selected residue tangent determines a point on the double-localized chart. -/
def chartResidue : TangentChart W →ₐ[R] K :=
  IsLocalization.Away.liftAlgHom (tangentDenom W)
    (f := tangentResidue W h6 r hr)
    (by rw [tangentResidue_denom]; exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hs))

lemma chartResidue_on_tangent (x : TangentRing W) :
    chartResidue W h6 r hr hs (algebraMap (TangentRing W) (TangentChart W) x) =
      tangentResidue W h6 r hr x :=
  by
    simp only [chartResidue, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
    rfl

/-- The residue point lies over the literal affine node (0,0) of W. -/
lemma chartResidue_affine_triangle :
    (chartResidue W h6 r hr hs).comp (IsScalarTower.toAlgHom R (W.toAffine.CoordinateRing)
      (TangentChart W)) =
      affineOrigin W h6 := by
  apply affine_ext
  · change chartResidue W h6 r hr hs (algebraMap (W.toAffine.CoordinateRing) (TangentChart W)
    (affineX W)) = _
    rw [IsScalarTower.algebraMap_apply (W.toAffine.CoordinateRing) (TangentRing W),
      chartResidue_on_tangent]
    simp [affineOrigin, tangentResidue]
  · change chartResidue W h6 r hr hs (algebraMap (W.toAffine.CoordinateRing) (TangentChart W)
    (affineY W)) = _
    rw [IsScalarTower.algebraMap_apply (W.toAffine.CoordinateRing) (TangentRing W),
      chartResidue_on_tangent]
    simp [affineOrigin, tangentResidue]

/-- The residue point lies over the literal node origin under U=Y−TX, V=Y+(a₁+T)X. -/
lemma chartResidue_node_triangle (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) :
    (chartResidue W h6 r hr hs).comp
      ((IsScalarTower.toAlgHom R (TangentRing W) (TangentChart W)).comp (nodeToTangent W h3 h4)) =
      nodeOrigin W h6 := by
  apply PlaneNode.hom_ext
  · change chartResidue W h6 r hr hs
      (algebraMap (TangentRing W) (TangentChart W) (nodeToTangent W h3 h4 (PlaneNode.U W.a₆))) = _
    rw [chartResidue_on_tangent]
    simp [nodeToTangent, nodeOrigin]
  · change chartResidue W h6 r hr hs
      (algebraMap (TangentRing W) (TangentChart W) (nodeToTangent W h3 h4 (PlaneNode.V W.a₆))) = _
    rw [chartResidue_on_tangent]
    simp [nodeToTangent, nodeOrigin]

include hr in
/-- Unit b₂ makes every split tangent root simple, also in characteristic two. -/
lemma tangent_simple_of_b₂_unit (hb : IsUnit W.b₂) : 2 * r + algebraMap R K W.a₁ ≠ 0 := by
  have hb' : algebraMap R K W.b₂ ≠ 0 := (hb.map (algebraMap R K)).ne_zero
  have he : (2 * r + algebraMap R K W.a₁) ^ 2 = algebraMap R K W.b₂ := by
    simp only [WeierstrassCurve.b₂, map_add, map_mul, map_pow, map_ofNat]
    linear_combination 4 * hr
  intro h
  rw [h, zero_pow (by decide)] at he
  exact hb' he.symm
end FieldPoint

variable (W : WeierstrassCurve R) (h3 : W.a₃ = 0) (h4 : W.a₄ = 0)

lemma tangentEquiv_node_triangle :
    (tangentEquiv W h3 h4).toAlgHom.comp (nodeToTangent W h3 h4) =
      IsScalarTower.toAlgHom R (PlaneNode.Ring W.a₆) (NodeTangentRing W) := by
  change (tangentToNodeTangent W h3 h4).comp (nodeToTangent W h3 h4) = _
  apply PlaneNode.hom_ext
  · simp only [AlgHom.comp_apply, nodeToTangent, PlaneNode.lift_U, map_sub, map_mul,
      tangentToNodeTangent_y, tangentToNodeTangent_t, tangentToNodeTangent_x]
    change nodeTangentY W - nodeTangentT W * nodeTangentX W = nodeTangentU W
    simp [nodeTangentY]
  · simp only [AlgHom.comp_apply, nodeToTangent, PlaneNode.lift_V, map_add, map_mul,
      AlgHom.commutes, tangentToNodeTangent_y, tangentToNodeTangent_t, tangentToNodeTangent_x]
    change nodeTangentY W + (algebraMap R _ W.a₁ + nodeTangentT W) * nodeTangentX W = nodeTangentV W
    have h := nodeTangent_relation W
    dsimp [nodeTangentY]
    linear_combination h

lemma chartEquiv_node_triangle (z : PlaneNode.Ring W.a₆) :
    chartEquiv W h3 h4 (algebraMap (TangentRing W) (TangentChart W) (nodeToTangent W h3 h4 z)) =
      algebraMap (PlaneNode.Ring W.a₆) (NodeChart W) z := by
  rw [chartEquiv_on_tangent]
  have h := congrArg (fun f : PlaneNode.Ring W.a₆ →ₐ[R] NodeTangentRing W => f z)
    (tangentEquiv_node_triangle W h3 h4)
  change tangentEquiv W h3 h4 (nodeToTangent W h3 h4 z) =
    algebraMap (PlaneNode.Ring W.a₆) (NodeTangentRing W) z at h
  rw [h, ← IsScalarTower.algebraMap_apply]
end WeierstrassCurve.Affine.TangentNode

/- Migration source: R5Lab/AlgebraicGeometry/Curves/Nodal/SplitChart.lean,
frozen packet f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 cbe0ba17c6043949ad0cda88aa7cfb298eb19a8d8f70adc0f00f4eefd62e8927.
Shared affine coordinates and PlaneNode carriers are reused without aliases. -/
