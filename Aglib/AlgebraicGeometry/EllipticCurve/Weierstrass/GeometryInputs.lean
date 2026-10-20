/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.AffineComplement
public import Aglib.AlgebraicGeometry.Curves.Core
public import Aglib.AlgebraicGeometry.Curves.Genus

/-!
# The exact remaining geometry and pointed-isomorphism inputs

Source: ordinary R5 Weierstrass.Projective, lines 351–355 and 1016–1028.
These are explicit unresolved supplier statements. They prove neither
nonsingular geometry of the literal Proj nor j-invariance for arbitrary
pointed projective isomorphisms. Properness is already proved separately.
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
open AlgebraicGeometry.Scheme.OverField.Curve
namespace WeierstrassCurve.Projective
universe u
attribute [local instance] Over.cartesianMonoidalCategory

/-- Geometry and coherent genus of the same literal nonsingular Proj cubic,
uniform over every field. A proof of this family remains a separate input. -/
def NonsingularWeierstrassGeometry : Prop :=
  ∀ (k : Type u) [Field k] (W : WeierstrassCurve k), W.Δ ≠ 0 →
    Properties (curveOver W) ∧ coherentGenus k (curveOver W) = 1

/-- The original all-fields pointed-projective j-invariance input. An affine
variable-change isomorphism alone does not supply this assertion. -/
def PointedWeierstrassJInvariant : Prop :=
  ∀ (k : Type u) [Field k] (W V : WeierstrassCurve k),
    W.Δ ≠ 0 → V.Δ ≠ 0 → ∀ e : curveOver W ≅ curveOver V,
      originOver W ≫ e.hom = originOver V → W.c₄ ^ 3 / W.Δ = V.c₄ ^ 3 / V.Δ

end WeierstrassCurve.Projective
