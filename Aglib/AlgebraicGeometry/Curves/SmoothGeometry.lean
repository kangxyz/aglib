/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Basic
public import Aglib.AlgebraicGeometry.Geometrically.Integral.SmoothCurve
public import Aglib.AlgebraicGeometry.Group.PointedMorphism
public import Aglib.AlgebraicGeometry.SchemeOverField

/-!
# Smooth curve geometry at the pointed-isogeny interface

Source: `K2-018#prop:k2018-arithmetic-characters`,
`research/exposes/K2/018/expose.tex`, lines 341–445 at revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, source SHA-256
`e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.
The rational-origin application also supplies auxiliary local geometry for
`K2-018#sec:k2018-splitting`, lines 240–249, and
`K2-018#lem:k2018-residue-bockstein`, lines 308–339, at the same snapshot.

The exact smooth relative-dimension-one and geometric-connectedness fields of
`Properties` give geometric integrality. Consequently an origin-preserving
morphism between the actual proper curve group schemes is a homomorphism.
The actual rational-origin local ring is a DVR when its structure morphism
agrees with that of the curve. No integrality or local-domain input is supplied.

These results do not realize coherent-cohomological genus, prove Riemann--Hurwitz,
construct a genus-one group law, or prove a Galois or Quillen comparison.

Implementation basis: `6987216b7dfb16036f94cc41b3c33a2da4e5e535`;
Lean `4.34.1`, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
-/

open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)



@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.OverField.Curve
universe u
variable {F : Type u} [Field F]
attribute [local instance] Over.cartesianMonoidalCategory

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned source above:
the actual smooth geometrically connected curve is geometrically integral.
Properness is present in the exact consumer but unnecessary for this implication. -/
lemma Properties.isGeometricallyIntegral {X : FScheme F} (curve : Properties X) :
    GeometricallyIntegral X.hom := by
  let := curve.smooth
  let := curve.connected
  exact Scheme.geometricallyIntegral_of_smoothOfRelativeDimension_one_of_geometricallyConnected
    X.hom

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned source above:
the underlying actual curve scheme is integral, with no added global premise. -/
lemma Properties.isIntegral {X : FScheme F} (curve : Properties X) :
    IsIntegral X.left := by
  let := curve.isGeometricallyIntegral
  exact GeometricallyIntegral.isIntegral_of_subsingleton X.hom

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned source above:
the exact `GeometryBackground.pointedMorphism` field is proved from the two
actual curve conditions and the identity-section equation. -/
theorem pointedMorphism_of_curveProperties (G H : Grp (FScheme F))
    (curveG : Properties G.X) (curveH : Properties H.X)
    (f : G.X ⟶ H.X) (hf : η[G.X] ≫ f = η[H.X]) : IsMonHom f := by
  let := G.grp
  let := H.grp
  let := curveG.proper
  let := curveH.proper
  let := curveG.isGeometricallyIntegral
  exact Scheme.Group.PointedMorphism.isMonHom_of_geometricallyIntegral G.X H.X f hf

/-- Auxiliary geometry for `K2-018#sec:k2018-splitting` and
`K2-018#lem:k2018-residue-bockstein`, pinned source above: an actual rational
origin of a `Properties` scheme has a DVR local ring. The equality records
that its structure morphism is the actual curve's structure morphism. -/
lemma Properties.rationalOrigin_isDiscreteValuationRing {X : FScheme F}
    (curve : Properties X) (q : RationalPoint F X.left)
    (hstructure : q.structureMap = X.hom) :
    letI := curve.isIntegral
    IsDiscreteValuationRing q.localRing := by
  let := curve.isIntegral
  have : SmoothOfRelativeDimension 1 q.structureMap := by
    rw [hstructure]
    exact curve.smooth
  exact q.localRing_isDiscreteValuationRing_of_smoothOfRelativeDimension_one

end AlgebraicGeometry.Scheme.OverField.Curve
