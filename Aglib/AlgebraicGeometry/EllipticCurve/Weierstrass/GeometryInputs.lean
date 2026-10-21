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
# Exact geometry and pointed-isomorphism interfaces

Source: ordinary R5 Weierstrass.Projective, lines 351–355 and 1016–1028.
These retained statements describe the same literal Proj and infinity
section. Geometry supplies the nonsingular-geometry family, and
PointedIsomorphism supplies j-invariance for arbitrary pointed projective
isomorphisms. The interfaces remain separate from their proof modules.
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
uniform over every field. Geometry supplies the proved family. -/
def NonsingularWeierstrassGeometry : Prop :=
  ∀ (k : Type u) [Field k] (W : WeierstrassCurve k), W.Δ ≠ 0 →
    Properties (curveOver W) ∧ coherentGenus k (curveOver W) = 1

/-- The original all-fields pointed-projective j-invariance interface.
PointedIsomorphism derives the requisite variable change from the given
pointed projective isomorphism and supplies the proved family. -/
def PointedWeierstrassJInvariant : Prop :=
  ∀ (k : Type u) [Field k] (W V : WeierstrassCurve k),
    W.Δ ≠ 0 → V.Δ ≠ 0 → ∀ e : curveOver W ≅ curveOver V,
      originOver W ≫ e.hom = originOver V → W.c₄ ^ 3 / W.Δ = V.c₄ ^ 3 / V.Δ

end WeierstrassCurve.Projective
