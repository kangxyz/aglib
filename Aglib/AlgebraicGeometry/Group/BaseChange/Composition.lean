/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.BaseChange.PointTransport
public import Aglib.AlgebraicGeometry.Group.ScalarExtension

/-!
# Equality of the two canonical group-pullback composition maps

The point-transport and scalar-extension constructors have the same
actual forward group-object morphism, for arbitrary composable scheme maps.

Source: `R5Lab.Aglib.AlgebraicGeometry.Group.BaseChange.Composition`
at R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`0b74b8b64b0306050c00b5d2ac5b147561f01a4b12e8f1ff4074815c4d659aed`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

open AlgebraicGeometry.Scheme.Group.BaseChange.PointTransport

namespace AlgebraicGeometry.Scheme.Group.BaseChange

universe u
attribute [local instance] Over.cartesianMonoidalCategory

/-- The two existing group-object pullback associators are the same actual map. -/
theorem groupPullbackCompIso_eq {S T U : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ U) (A : Grp (Over U)) :
    groupPullbackCompIso f g A = (groupSchemeBaseChangeComp f g).symm.app A := by
  apply Iso.ext
  apply Grp.hom_ext
  rw [groupPullbackCompIso_hom]
  exact (groupSchemeBaseChangeComp_inv_app_hom_hom f g A).symm

end AlgebraicGeometry.Scheme.Group.BaseChange
