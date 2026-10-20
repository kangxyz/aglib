/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.ScalarExtension
public import Aglib.AlgebraicGeometry.Limits.OverRange

/-!
# The range of the actual base-changed group unit

The unit range is the inverse image of the original unit range under
the actual first pullback projection, over arbitrary scheme bases.

Source: `R5Lab.Aglib.AlgebraicGeometry.Group.BaseChange.UnitRange`
at R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`b0d400af861b147780c40c66ecbbffc8f316f4b9ecf4265eedb3a55c31edf22f`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

open AlgebraicGeometry.Scheme.Pullback

namespace AlgebraicGeometry.Scheme.Group.BaseChange

universe u
attribute [local instance] Over.cartesianMonoidalCategory

theorem range_unit_baseChange {S T : Scheme.{u}} (s : S ⟶ T)
    (G : Grp (Over T)) :
    Set.range (η[((groupSchemeBaseChange s).functor.obj G).X]).left =
      pullback.fst G.X.hom s ⁻¹' Set.range (η[G.X]).left := by
  have hη : (η[((groupSchemeBaseChange s).functor.obj G).X]).left =
      (Functor.LaxMonoidal.ε (Over.pullback s)).left ≫
        ((Over.pullback s).map (η[G.X])).left := rfl
  have : IsIso (Functor.LaxMonoidal.ε (Over.pullback s)).left := by
    rw [Over.ε_pullback_left]
    infer_instance
  rw [← range_pullbackMap s (η[G.X])]
  exact range_eq_range_of_surjective _ _ _ hη.symm

end AlgebraicGeometry.Scheme.Group.BaseChange
