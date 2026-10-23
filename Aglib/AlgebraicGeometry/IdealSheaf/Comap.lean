/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# The pullback square of a closed subscheme

For `b : Y ⟶ X` and a closed subscheme `I : X.IdealSheafData`, Mathlib's
`subschemeMap (I.comap b) I b (I.le_map_comap b) : (I.comap b).subscheme ⟶ I.subscheme` lies over
`b`. The square it forms with the two closed immersions is cartesian
(`Scheme.IdealSheafData.isPullback_subschemeMap_comap`), by Mathlib's
`isPullback_of_isClosedImmersion`: the pullback of `ker I.subschemeι = I` along `b` is
`ker (I.comap b).subschemeι = I.comap b`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- **The pullback of a closed subscheme is the fiber product**: the square
`(I.comap b).subscheme ⟶ I.subscheme` over `b : Y ⟶ X`, through Mathlib's `subschemeMap`, is
cartesian. -/
theorem isPullback_subschemeMap_comap (I : X.IdealSheafData) (b : Y ⟶ X) :
    IsPullback (subschemeMap (I.comap b) I b (I.le_map_comap b)) (I.comap b).subschemeι
      I.subschemeι b :=
  (isPullback_of_isClosedImmersion (I.comap b).subschemeι I.subschemeι
    (subschemeMap (I.comap b) I b (I.le_map_comap b)) b
    (subschemeMap_subschemeι _ _ _ _).symm (by simp)).flip

end AlgebraicGeometry.Scheme.IdealSheafData
