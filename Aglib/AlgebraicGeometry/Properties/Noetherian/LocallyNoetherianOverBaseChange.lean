/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyNoetherianOver
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Locally Noetherian test schemes along a change of base

Let `g : S' ⟶ S` be a morphism of schemes.

* `Scheme.LocallyNoetherianOver.map g : LocallyNoetherianOver S' ⥤ LocallyNoetherianOver S` is
  `Over.map g` on locally Noetherian test schemes: an `S'`-scheme `T` is an `S`-scheme through
  `T ⟶ S' ⟶ S`, with the same underlying scheme, so it stays locally Noetherian.
* For `S'` locally Noetherian and `Y ⟶ S` locally of finite type, the base change
  `(Over.pullback g).obj Y`, that is `Y ×_S S' ⟶ S'`, is locally of finite type
  (`Scheme.locallyOfFiniteType_over_pullback_obj_hom`) and its source is locally Noetherian
  (`Scheme.isLocallyNoetherian_over_pullback_obj_left`, from Mathlib's
  `LocallyOfFiniteType.isLocallyNoetherian`; Stacks, Tag 01T6). So
  `Scheme.LocallyNoetherianOver.baseChange g P` is `P ×_S S'` as a locally Noetherian
  `S'`-scheme, for `P` a locally Noetherian `S`-scheme locally of finite type over `S`.

Fibre products of locally Noetherian schemes need not be locally Noetherian; the finite-type
hypothesis on `P ⟶ S` is what makes `P ×_S S'` a test scheme. The consumer is the base change of a
scheme representing a functor on locally Noetherian test schemes
(`Aglib.AlgebraicGeometry.Picard.BaseChangeRepresentableBy`), with Mathlib's adjunction
`Over.mapPullbackAdj g : Over.map g ⊣ Over.pullback g`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {S S' : Scheme.{u}} (g : S' ⟶ S)

/-- `Y ×_S S'` is locally Noetherian when `S'` is locally Noetherian and `Y ⟶ S` is locally of
finite type. -/
instance isLocallyNoetherian_over_pullback_obj_left [IsLocallyNoetherian S'] (Y : Over S)
    [LocallyOfFiniteType Y.hom] : IsLocallyNoetherian ((Over.pullback g).obj Y).left :=
  inferInstanceAs (IsLocallyNoetherian (Limits.pullback Y.hom g))

/-- `Y ×_S S' ⟶ S'` is locally of finite type when `Y ⟶ S` is. -/
instance locallyOfFiniteType_over_pullback_obj_hom (Y : Over S) [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType ((Over.pullback g).obj Y).hom :=
  inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd Y.hom g))

/-- **`Over.map g` on locally Noetherian test schemes**: a locally Noetherian `S'`-scheme `T` is a
locally Noetherian `S`-scheme through `T ⟶ S' ⟶ S`, with the same underlying scheme. -/
def LocallyNoetherianOver.map : LocallyNoetherianOver S' ⥤ LocallyNoetherianOver S :=
  (locallyNoetherianOver S).lift ((locallyNoetherianOver S').ι ⋙ Over.map g) fun T => T.property

theorem LocallyNoetherianOver.map_obj_obj (T : LocallyNoetherianOver S') :
    ((LocallyNoetherianOver.map g).obj T).obj = (Over.map g).obj T.obj :=
  rfl

/-- **The base change `P ×_S S'`** of a locally Noetherian `S`-scheme `P` locally of finite type
over `S`, as a locally Noetherian `S'`-scheme for `S'` locally Noetherian: the object
`(Over.pullback g).obj P.obj`. -/
abbrev LocallyNoetherianOver.baseChange [IsLocallyNoetherian S'] (P : LocallyNoetherianOver S)
    [LocallyOfFiniteType P.obj.hom] : LocallyNoetherianOver S' :=
  ⟨(Over.pullback g).obj P.obj, inferInstance⟩

end AlgebraicGeometry.Scheme
