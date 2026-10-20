/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.AffineComplement
public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts

/-!
# The actual projective and affine Weierstrass function fields

Source: ordinary R5 Weierstrass.Projective, lines 1064–1081.
The generic-stalk carrier and its native constants are reused. Integrality
of the same literal cubic remains an explicit instance hypothesis.
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
variable {F : Type u} [Field F] (W : WeierstrassCurve F)
variable [IsIntegral (scheme W)]

/-- Its F-algebra structure is induced by the literal structural morphism. -/
instance schemeFunctionFieldAlgebra : Algebra F ((scheme W).functionField) :=
  (Scheme.functionFieldConstants (scheme W) (structureMap W)).toAlgebra

/-- Canonical affine-chart identification, built from its generic-stalk pullback
and the universal property of the fraction ring. -/
def affineFunctionFieldEquiv : (scheme W).functionField ≃ₐ[F] FractionRing (affineRing W) where
  __ := Scheme.FunctionField.affineFieldEquiv (.of (affineRing W)) (affineChart W)
  commutes' a := Scheme.FunctionField.affineFieldEquiv_constants
    (.of (affineRing W)) (affineChart W) F (structureMap W) (affineChart_structure W) a

/-- Actual projective function-field x-coordinate, identified through the
canonical chart rather than a freely chosen field isomorphism. -/
def functionX : (scheme W).functionField :=
  (affineFunctionFieldEquiv W).symm
    (algebraMap (affineRing W) (FractionRing (affineRing W)) (affineX W))

/-- Actual projective function-field y-coordinate through the same chart. -/
def functionY : (scheme W).functionField :=
  (affineFunctionFieldEquiv W).symm
    (algebraMap (affineRing W) (FractionRing (affineRing W)) (affineY W))


/-- The projective x-coordinate maps to the original affine x-coordinate. -/
@[simp] theorem affineFunctionFieldEquiv_functionX :
    affineFunctionFieldEquiv W (functionX W) =
      algebraMap (affineRing W) (FractionRing (affineRing W)) (affineX W) :=
  (affineFunctionFieldEquiv W).apply_symm_apply _

/-- The projective y-coordinate maps to the original affine y-coordinate. -/
@[simp] theorem affineFunctionFieldEquiv_functionY :
    affineFunctionFieldEquiv W (functionY W) =
      algebraMap (affineRing W) (FractionRing (affineRing W)) (affineY W) :=
  (affineFunctionFieldEquiv W).apply_symm_apply _

end WeierstrassCurve.Projective
