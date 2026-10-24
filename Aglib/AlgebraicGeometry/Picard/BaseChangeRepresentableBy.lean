/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.BaseChange
public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyNoetherianOverBaseChange
public import Aglib.CategoryTheory.ObjectProperty.RepresentableByAdjunction

/-!
# Base change of a scheme representing the fppf Picard sheaf

Let `p : X ⟶ S` and `g : S' ⟶ S` be morphisms of schemes with `S'` locally Noetherian, and put
`p' := pullback.snd p g : X ×_S S' ⟶ S'`. Suppose that the fppf Picard sheaf `Pic_{X/S,(fppf)}`
(`fppfPicardSheaf p`), restricted to locally Noetherian test schemes, is represented by `P` with
`P ⟶ S` locally of finite type:

`e : (T ⟶ P) ≃ Pic_{X/S,(fppf)}(T)`, natural in locally Noetherian `S`-schemes `T`.

Then `P ×_S S'` (the object `(Over.pullback g).obj P.obj`, `LocallyNoetherianOver.baseChange g P`)
is locally Noetherian and represents `Pic_{X'/S',(fppf)}`, where `X' = X ×_S S'`, on locally
Noetherian `S'`-schemes (`baseChangeRepresentableBy`). For a locally Noetherian `S'`-scheme `T`,
the bijection is

`(T ⟶ P ×_S S') ≃ (T ⟶ P) ≃ Pic_{X/S,(fppf)}(T) ≃ Pic_{X'/S',(fppf)}(T)`
(`baseChangeRepresentableBy_homEquiv`):

1. the adjunction `Over.map g ⊣ Over.pullback g` (Mathlib's `Over.mapPullbackAdj`), where on the
   right `T` is an `S`-scheme through `T ⟶ S' ⟶ S`; this does not change the scheme `T`, so `T` is
   still a locally Noetherian test scheme (`LocallyNoetherianOver.map g`);
2. the representation `e`;
3. the inverse of the base change `fppfPicardSheafBaseChangeIso p g` of the fppf Picard sheaf.

This is the representability part of Kleiman's base change of the Picard scheme (Kleiman, *The
Picard scheme*, arXiv:math/0504020v1, Ex. 4.4, p. 27, and Answer 4.4, p. 65): if `Pic_{X/S}`
exists, then `Pic_{X/S} ×_S S'` represents `Pic_{X'/S'}`.

Conditions: `S'` is locally Noetherian and `P ⟶ S` is locally of finite type. Then
`P ×_S S' ⟶ S'` is locally of finite type, hence `P ×_S S'` is locally Noetherian (Mathlib's
`LocallyOfFiniteType.isLocallyNoetherian`), which makes it a test scheme
(`Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyNoetherianOverBaseChange`). No hypothesis
on `p` or on `S` is used. As in the representation `e`, the test schemes are the locally Noetherian
`S'`-schemes; Kleiman works only with locally Noetherian schemes (p. 15), so these are also his test
schemes in Answer 4.4, and his `S'` is locally Noetherian. The representation `e` is an explicit
argument;
the existence of `P` (Kleiman, Thm 4.8, pp. 27–28) is not proved here.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.RelativePicard

variable {S S' X : Scheme.{u}} (p : X ⟶ S) (g : S' ⟶ S)

/-- The base change `fppfPicardSheafBaseChangeIso p g` of the fppf Picard sheaf, restricted to
locally Noetherian `S'`-schemes, as an isomorphism of presheaves of sets: `Pic_{X/S,(fppf)}(T)`,
for `T` viewed over `S`, is `Pic_{X'/S',(fppf)}(T)`. -/
def locallyNoetherianFppfPicardSheafBaseChangeIso :
    (LocallyNoetherianOver.map g).op ⋙ (locallyNoetherianOverInclusion S).op ⋙
        (fppfPicardSheaf p).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1} ≅
      (locallyNoetherianOverInclusion S').op ⋙ (fppfPicardSheaf (pullback.snd p g)).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerLeft (locallyNoetherianOverInclusion S').op
    (Functor.isoWhiskerRight (fppfPicardSheafBaseChangeIso p g).symm
      (CategoryTheory.forget AddCommGrpCat.{u + 1}))

variable [IsLocallyNoetherian S'] (P : LocallyNoetherianOver S) [LocallyOfFiniteType P.obj.hom]
  (e : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- **Base change of the Picard scheme** (Kleiman, *The Picard scheme*, arXiv:math/0504020v1,
Ex. 4.4, p. 27, and Answer 4.4, p. 65): if `P`, locally of finite type over `S`, represents
`Pic_{X/S,(fppf)}` on locally Noetherian test schemes, and `S'` is locally Noetherian, then
`P ×_S S'` represents `Pic_{X'/S',(fppf)}` on locally Noetherian `S'`-schemes, where
`X' = X ×_S S'`. -/
def baseChangeRepresentableBy :
    ((locallyNoetherianOverInclusion S').op ⋙ (fppfPicardSheaf (pullback.snd p g)).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy
        (LocallyNoetherianOver.baseChange g P) :=
  (ObjectProperty.representableByLiftOfAdjunction (P := locallyNoetherianOver S')
    (Q := locallyNoetherianOver S) (Over.mapPullbackAdj g) (fun T => T.property) e
    (LocallyNoetherianOver.baseChange g P).property).ofIso
    (locallyNoetherianFppfPicardSheafBaseChangeIso p g)

/-- **The bijection of `baseChangeRepresentableBy`**: a morphism `f : T ⟶ P ×_S S'` of
`S'`-schemes goes to the morphism `T ⟶ P` of `S`-schemes given by the adjunction
`Over.map g ⊣ Over.pullback g`, then to its class under `e`, then to `Pic_{X'/S',(fppf)}(T)` by the
inverse of the base change of the fppf Picard sheaf. -/
theorem baseChangeRepresentableBy_homEquiv {T : LocallyNoetherianOver S'}
    (f : T ⟶ LocallyNoetherianOver.baseChange g P) :
    (baseChangeRepresentableBy p g P e).homEquiv f =
      ((fppfPicardSheafBaseChangeIso p g).inv.app (op T.obj)).hom
        (e.homEquiv
          (ObjectProperty.homMk (((Over.mapPullbackAdj g).homEquiv T.obj P.obj).symm f.hom) :
            (LocallyNoetherianOver.map g).obj T ⟶ P)) :=
  rfl

end AlgebraicGeometry.Scheme.RelativePicard
