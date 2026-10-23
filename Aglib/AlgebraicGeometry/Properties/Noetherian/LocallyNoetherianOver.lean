/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Locally Noetherian schemes over a base

For a scheme `S`, `Scheme.locallyNoetherianOver S` is the property of an object `T ⟶ S` of
`Over S` that `T` is locally Noetherian, and `Scheme.LocallyNoetherianOver S` is its full
subcategory: locally Noetherian schemes over `S` with all morphisms over `S`. The inclusion into
`Over S` is `Scheme.locallyNoetherianOverInclusion S`, and every object carries the instance
`IsLocallyNoetherian T.obj.left` (`Scheme.LocallyNoetherianOver.isLocallyNoetherian`).

These are the test schemes of the representability statements of Nitsure, *Construction of
Hilbert and Quot schemes*, arXiv:math/0504590v1: the Hilbert and Quot functors are considered on
locally Noetherian schemes over the base (§1, pp. 3–4), and the embedding of `Hilb^Φ` into a
Grassmannian is a morphism of such functors (§5, p. 26). Only objects are restricted; the
morphisms are all morphisms over `S`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The property of an object `T ⟶ S` of `Over S` that `T` is locally Noetherian. -/
abbrev locallyNoetherianOver (S : Scheme.{u}) : ObjectProperty (Over S) :=
  fun T => IsLocallyNoetherian T.left

/-- **Locally Noetherian test schemes over `S`**: the full subcategory of `Over S` on the objects
`T ⟶ S` with `T` locally Noetherian, with all morphisms over `S` (Nitsure,
arXiv:math/0504590v1, §1, pp. 3–4). -/
abbrev LocallyNoetherianOver (S : Scheme.{u}) := (locallyNoetherianOver S).FullSubcategory

/-- The underlying scheme of a locally Noetherian test scheme is locally Noetherian. -/
instance LocallyNoetherianOver.isLocallyNoetherian {S : Scheme.{u}} (T : LocallyNoetherianOver S) :
    IsLocallyNoetherian T.obj.left :=
  T.property

/-- The inclusion of locally Noetherian test schemes over `S` into `Over S`. -/
abbrev locallyNoetherianOverInclusion (S : Scheme.{u}) : LocallyNoetherianOver S ⥤ Over S :=
  (locallyNoetherianOver S).ι

end AlgebraicGeometry.Scheme
