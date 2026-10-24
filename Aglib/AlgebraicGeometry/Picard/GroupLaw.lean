/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Fppf
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.CommGrpObj

/-!
# The group law of a scheme representing the fppf Picard sheaf

Let `S` be a locally Noetherian scheme and `p : X ⟶ S` a morphism. Suppose that the fppf Picard
sheaf `Pic_{X/S,(fppf)}` (`fppfPicardSheaf p`, the fppf sheafification of
`T ↦ Pic(X ×_S T) / Pic(T)`; Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Def. 2.2,
p. 17), restricted to locally Noetherian test schemes, is represented by `P` with `P ⟶ S` locally
of finite type:

`e : (T ⟶ P) ≃ Pic_{X/S,(fppf)}(T)`, natural in locally Noetherian `S`-schemes `T`.

Then `P` is a commutative group object of `Over S` (`picardCommGrpObj`), and `e` is an
isomorphism of abelian groups on `T`-points for every locally Noetherian `T`
(`picardHomAddEquiv`, `picard_homEquiv_mul`, `picard_homEquiv_one`, `picard_homEquiv_inv`). This
is the group scheme structure of the Picard scheme `Pic_{X/S}` when it represents
`Pic_{X/S,(fppf)}` (Kleiman, Def. 4.1, p. 26, for the Picard scheme; Stacks, Tag 022S, for group
schemes through their functors of points); Kleiman uses it in Prop. 5.3, p. 37, through the
group-scheme Lemma 5.1, pp. 36–37.

The representation `e` is an explicit argument. Its existence, the representability of
`Pic_{X/S,(fppf)}` (Kleiman, Thm 4.8, pp. 27–28, with the remark after Def. 4.1, p. 26), is not
proved here. The construction is `LocallyNoetherianOver.commGrpObjOfRepresentableBy` for the
presheaf `(fppfPicardSheaf p).obj`; no hypothesis on `p` is used.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.LocallyNoetherianOver

variable {S X : Scheme.{u}} [IsLocallyNoetherian S] (p : X ⟶ S) (P : LocallyNoetherianOver S)
  [LocallyOfFiniteType P.obj.hom]
  (e : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- **The group law of the Picard scheme.** If `Pic_{X/S,(fppf)}` on locally Noetherian test
schemes is represented by `P` locally of finite type over the locally Noetherian base `S`, then
`P` is a commutative group object of `Over S`. -/
@[instance_reducible]
def picardCommGrpObj : CommGrpObj P.obj :=
  commGrpObjOfRepresentableBy (fppfPicardSheaf p).obj P e

open scoped CategoryTheory.MonObj

/-- The representation `e` sends the identity of the group law to the zero class. -/
theorem picard_homEquiv_one (T : LocallyNoetherianOver S) :
    letI := picardCommGrpObj p P e
    e.homEquiv (ObjectProperty.homMk (1 : T.obj ⟶ P.obj)) =
      (0 : (fppfPicardSheaf p).obj.obj (op T.obj)) :=
  homEquiv_one (fppfPicardSheaf p).obj P e T

/-- **The group law of `P` is the addition of `Pic_{X/S,(fppf)}`** on locally Noetherian points:
`e (f * g) = e f + e g`. -/
theorem picard_homEquiv_mul {T : LocallyNoetherianOver S} (f g : T.obj ⟶ P.obj) :
    letI := picardCommGrpObj p P e
    e.homEquiv (ObjectProperty.homMk (f * g)) =
      e.homEquiv' (F := (locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj)
          (ObjectProperty.homMk f) +
        e.homEquiv' (F := (locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj)
          (ObjectProperty.homMk g) :=
  homEquiv_mul (fppfPicardSheaf p).obj P e f g

/-- The representation `e` sends the inverse of the group law to the negative class. -/
theorem picard_homEquiv_inv {T : LocallyNoetherianOver S} (f : T.obj ⟶ P.obj) :
    letI := picardCommGrpObj p P e
    e.homEquiv (ObjectProperty.homMk f⁻¹) =
      -e.homEquiv' (F := (locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj)
        (ObjectProperty.homMk f) :=
  homEquiv_inv (fppfPicardSheaf p).obj P e f

/-- **Points of the Picard scheme as a group**: for every locally Noetherian `S`-scheme `T`, the
representation `e` is an isomorphism of abelian groups from `T ⟶ P` (written additively) to
`Pic_{X/S,(fppf)}(T)`. -/
def picardHomAddEquiv (T : LocallyNoetherianOver S) :
    letI := picardCommGrpObj p P e
    Additive (T.obj ⟶ P.obj) ≃+ (fppfPicardSheaf p).obj.obj (op T.obj) :=
  homAddEquiv (fppfPicardSheaf p).obj P e T

@[simp]
theorem picardHomAddEquiv_apply (T : LocallyNoetherianOver S) (f : T.obj ⟶ P.obj) :
    letI := picardCommGrpObj p P e
    picardHomAddEquiv p P e T (Additive.ofMul f) = e.homEquiv (ObjectProperty.homMk f) :=
  rfl

end AlgebraicGeometry.Scheme.RelativePicard
