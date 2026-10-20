/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.SchemeOverField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Field curves and prescribed-origin group laws

The actual smooth proper geometrically connected curve predicate and the native
`GrpObj` data with a prescribed rational origin. Migrated from
`R5Lab.Aglib.AlgebraicGeometry.Curves.Basic` at R5Lab revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, preserving its full fields and universes.
The group law is data and is not constructed by the curve properties.
-/




@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.OverField

universe u
variable {F : Type u} [Field F]
attribute [local instance] Over.cartesianMonoidalCategory

/-- Smooth proper geometrically connected dimension-one field schemes. -/
structure Curve.Properties (X : FScheme F) : Prop where
  smooth : SmoothOfRelativeDimension 1 X.hom
  proper : IsProper X.hom
  connected : GeometricallyConnected X.hom

/-- Native group-object data on the actual field scheme, with the specified origin. -/
structure PointedGroupLaw (X : FScheme F) (o : 𝟙_ (FScheme F) ⟶ X) where
  /-- The group-object structure on `X` whose identity is required to equal the prescribed
  origin. -/
  law : GrpObj X
  origin : @MonObj.one _ _ _ X law.toMonObj = o

end AlgebraicGeometry.Scheme.OverField
