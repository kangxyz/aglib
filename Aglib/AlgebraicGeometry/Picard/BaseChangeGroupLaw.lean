/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.BaseChangeRepresentableBy
public import Aglib.AlgebraicGeometry.Picard.GroupLaw
public import Aglib.CategoryTheory.Monoidal.AdjunctionHomMulEquiv
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# The group law of the base change of a scheme representing the fppf Picard sheaf

Let `S` and `S'` be locally Noetherian schemes, `p : X ⟶ S` and `g : S' ⟶ S` morphisms, and
`p' := pullback.snd p g : X ×_S S' ⟶ S'`. Let `P`, locally of finite type over `S`, represent the
fppf Picard sheaf `Pic_{X/S,(fppf)}` on locally Noetherian test schemes through `e`. Then
`P ×_S S'` carries two group laws over `S'`:

* the group law of a scheme representing `Pic_{X'/S',(fppf)}` on locally Noetherian test schemes,
  for the representation `baseChangeRepresentableBy p g P e`: `picardCommGrpObj` for `p'`, the
  object `LocallyNoetherianOver.baseChange g P` and that representation;
* the base change along `Over.pullback g` of the group law `picardCommGrpObj p P e` of `P`:
  Mathlib's `Functor.grpObjObj` for the monoidal functor `Over.pullback g`, the group law of
  `(Over.pullback g).mapGrp` (and so of Mathlib's `Over.grpObjMkPullbackSnd` and of Aglib's
  `Scheme.Group.BaseChange.groupSchemeBaseChange g`).

They are equal (`picardCommGrpObj_baseChange_toGrpObj`): the Picard scheme commutes with base
change as a group scheme (Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Ex. 4.4, p. 27, and
Answer 4.4, p. 65, for the base change of the Picard scheme, and Def. 4.1, p. 26, for the Picard
scheme; Stacks, Tag 022S, for group schemes through their functors of points).

Both laws make the representation additive on locally Noetherian points. For the base-changed
law this is `baseChangeRepresentableBy_homEquiv_mul`: the adjunction bijection
`(T ⟶ P ×_S S') ≃ (T ⟶ P)` is multiplicative (`Adjunction.homEquiv_symm_mul`), and so are `e`
(`picard_homEquiv_mul`) and the base change of the fppf Picard sheaf. A group law on `P ×_S S'` is
determined by the additivity of the representation at the test scheme
`(P ×_S S') ×_{S'} (P ×_S S')`, which is locally of finite type over the locally Noetherian `S'`,
hence locally Noetherian; its multiplication is the product of the two projections.

Conditions: `S` and `S'` locally Noetherian (`S` is a test scheme for the group law of `P`, and
`S'` for that of `P ×_S S'`), and `P ⟶ S` locally of finite type. The representation `e` is an
explicit argument.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.Scheme.RelativePicard

variable {S S' X : Scheme.{u}} [IsLocallyNoetherian S] [IsLocallyNoetherian S'] (p : X ⟶ S)
  (g : S' ⟶ S) (P : LocallyNoetherianOver S) [LocallyOfFiniteType P.obj.hom]
  (e : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- **The base-changed group law makes the base-changed representation additive**: for the group
law of `P ×_S S'` obtained from that of `P` by base change along `g` (`Functor.grpObjObj` for
`Over.pullback g`), the representation `baseChangeRepresentableBy p g P e` sends products of
points to sums, for every locally Noetherian `S'`-scheme `T`. -/
theorem baseChangeRepresentableBy_homEquiv_mul {T : LocallyNoetherianOver S'}
    (f₁ f₂ : T.obj ⟶ (Over.pullback g).obj P.obj) :
    letI := picardCommGrpObj p P e
    (baseChangeRepresentableBy p g P e).homEquiv (ObjectProperty.homMk (f₁ * f₂)) =
      (baseChangeRepresentableBy p g P e).homEquiv'
          (F := (locallyNoetherianOverInclusion S').op ⋙ (fppfPicardSheaf (pullback.snd p g)).obj)
          (ObjectProperty.homMk f₁) +
        (baseChangeRepresentableBy p g P e).homEquiv'
          (F := (locallyNoetherianOverInclusion S').op ⋙ (fppfPicardSheaf (pullback.snd p g)).obj)
          (ObjectProperty.homMk f₂) := by
  let := picardCommGrpObj p P e
  have h₁ := (Over.mapPullbackAdj g).homEquiv_symm_mul f₁ f₂
  have h₂ := picard_homEquiv_mul p P e (T := (LocallyNoetherianOver.map g).obj T)
    (((Over.mapPullbackAdj g).homEquiv T.obj P.obj).symm f₁)
    (((Over.mapPullbackAdj g).homEquiv T.obj P.obj).symm f₂)
  refine (congrArg (fun z => ((fppfPicardSheafBaseChangeIso p g).inv.app (op T.obj)).hom
    (e.homEquiv (ObjectProperty.homMk z : (LocallyNoetherianOver.map g).obj T ⟶ P))) h₁).trans ?_
  refine (congrArg ((fppfPicardSheafBaseChangeIso p g).inv.app (op T.obj)).hom h₂).trans ?_
  exact map_add _ _ _

/-- **The group law of the base change of the Picard scheme**: the group law of `P ×_S S'` as the
scheme representing `Pic_{X'/S',(fppf)}` on locally Noetherian test schemes
(`baseChangeRepresentableBy`) is the base change along `g` of the group law of `P`. -/
theorem picardCommGrpObj_baseChange_toGrpObj :
    letI := picardCommGrpObj p P e
    (picardCommGrpObj (pullback.snd p g) (LocallyNoetherianOver.baseChange g P)
        (baseChangeRepresentableBy p g P e)).toGrpObj =
      Functor.grpObjObj (F := Over.pullback g) (G := P.obj) := by
  let := picardCommGrpObj p P e
  -- the test scheme `(P ×_S S') ×_{S'} (P ×_S S')`, locally of finite type over `S'`
  have hW : locallyNoetherianOver S'
      ((Over.pullback g).obj P.obj ⊗ (Over.pullback g).obj P.obj) := by
    have : LocallyOfFiniteType
        ((Over.pullback g).obj P.obj ⊗ (Over.pullback g).obj P.obj).hom := by
      change LocallyOfFiniteType (pullback.fst _ _ ≫ _)
      infer_instance
    exact LocallyOfFiniteType.isLocallyNoetherian
      ((Over.pullback g).obj P.obj ⊗ (Over.pullback g).obj P.obj).hom
  -- the multiplication of a monoid law on `Q` is the product of the two projections
  have key {Q : Over S'} (m : MonObj Q) : (letI := m; fst Q Q * snd Q Q) = m.mul := by
    change lift (fst Q Q) (snd Q Q) ≫ m.mul = m.mul
    rw [lift_fst_snd, Category.id_comp]
  have k₁ := picard_homEquiv_mul (pullback.snd p g) (LocallyNoetherianOver.baseChange g P)
    (baseChangeRepresentableBy p g P e) (T := ⟨_, hW⟩) (fst _ _) (snd _ _)
  have k₂ := baseChangeRepresentableBy_homEquiv_mul p g P e (T := ⟨_, hW⟩) (fst _ _) (snd _ _)
  have k := congrArg InducedCategory.Hom.hom
    ((baseChangeRepresentableBy p g P e).homEquiv.injective (k₁.trans k₂.symm))
  exact GrpObj.ext _ _ (MonObj.ext _ _ ((key _).symm.trans (k.trans (key _))))

end AlgebraicGeometry.Scheme.RelativePicard
