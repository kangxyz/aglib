/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Cartesian

/-!
# Base-change mates of equal squares

The cartesian base-change mate `cartesianBaseChangeMap a b f g h` depends on the morphisms of the
square only up to the canonical comparisons `pullbackCongr`: for `a = a'` and `g = g'`,
`cartesianBaseChangeMap_congr` relates the mates of the two squares. This lets one compare the
mate of a pasted square `b ≫ a`, `v ≫ g` with the mate of a square written with equal composites,
as in the transitivity of base change (`cartesianBaseChangeMap_comp`). Arbitrary module sheaves; no
hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- **Mates of equal squares**: for `a = a'` and `g = g'`, the base-change mates of the cartesian
squares `(a, b, f, g)` and `(a', b, f, g')` agree up to `pullbackCongr`. -/
theorem cartesianBaseChangeMap_congr {W X T S : Scheme.{u}} {a a' : W ⟶ X} (b : W ⟶ T)
    (f : X ⟶ S) {g g' : T ⟶ S} (ha : a = a') (hg : g = g') (h : IsPullback a b f g)
    (h' : IsPullback a' b f g') (M : X.Modules) :
    (pullbackCongr hg).inv.app ((pushforward f).obj M) ≫
        (cartesianBaseChangeMap a b f g h).app M =
      (cartesianBaseChangeMap a' b f g' h').app M ≫
        (pushforward b).map ((pullbackCongr ha).inv.app M) := by
  subst ha
  subst hg
  simp [pullbackCongr]

end AlgebraicGeometry.Scheme.Modules
