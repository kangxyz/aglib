/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyOfFiniteTypeOver
public import Aglib.CategoryTheory.ObjectProperty.GrpObj
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

/-!
# The group law of a scheme representing a presheaf of abelian groups

Let `S` be a locally Noetherian scheme and `F : (Over S)ᵒᵖ ⥤ AddCommGrpCat` a presheaf of abelian
groups on schemes over `S`, with values in any universe. Suppose that the restriction of `F` to
locally Noetherian test schemes is represented by `P`, with `P ⟶ S` locally of finite type:

`e : (T ⟶ P) ≃ F(T)`, natural in locally Noetherian `S`-schemes `T`.

Then `P` is a commutative group object of `Over S`, for the cartesian monoidal structure by fibre
products over `S` (`LocallyNoetherianOver.commGrpObjOfRepresentableBy`), and `e` turns the group
law of `T ⟶ P` into the addition of `F(T)` for every locally Noetherian `T`
(`LocallyNoetherianOver.homEquiv_mul`, `homEquiv_one`, `homEquiv_inv`, and the bundled
`LocallyNoetherianOver.homAddEquiv`). This is the Yoneda construction of the group law of a
scheme whose functor of points is a functor to groups (Stacks, Tag 022S: a group scheme over `S`
is a scheme `G` over `S` with a multiplication `G ×_S G ⟶ G` making every `G(T)` a group), with
the test schemes restricted to locally Noetherian ones.

The products `P ×_S P` and `P ×_S P ×_S P` are needed as test schemes. They are locally of
finite type over `S`, hence locally Noetherian, whereas fibre products of locally Noetherian
schemes need not be locally Noetherian. The construction therefore runs in the full subcategory
`LocallyOfFiniteTypeOver S`, which is closed under finite products:

1. `e` restricts to schemes locally of finite type over `S`
   (`LocallyNoetherianOver.representableByLocallyOfFiniteType`), and composing `F` with Mathlib's
   `AddCommGrpCat.toCommGrp` gives a representation of a presheaf of commutative groups
   (`LocallyNoetherianOver.commGrpRepresentableBy`);
2. Mathlib's `CommGrpObj.ofRepresentableBy` gives the commutative group object of
   `LocallyOfFiniteTypeOver S` (`LocallyNoetherianOver.locallyOfFiniteTypeCommGrpObj`), for the
   braiding `BraidedCategory.ofCartesianMonoidalCategory`, a local instance here;
3. `CommGrpObj.ofFullSubcategory` carries it to `P` in `Over S`, with the same unit,
   multiplication and inverse.

Conditions: `S` is locally Noetherian, so that `S` itself is a test scheme (the unit of the group
law is a point over `S`), and `P ⟶ S` is locally of finite type. No other hypothesis on `F`.
-/

@[expose] public section

noncomputable section

universe w u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry.Scheme.LocallyNoetherianOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S] (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{w})
  (P : LocallyNoetherianOver S) [LocallyOfFiniteType P.obj.hom]
  (e : ((locallyNoetherianOverInclusion S).op ⋙ F ⋙
    CategoryTheory.forget AddCommGrpCat).RepresentableBy P)

/-- The cartesian braiding of schemes locally of finite type over `S`, used for the commutative
group objects of this file. It is named explicitly: a local instance still has a public name. -/
local instance braidedCategoryLocallyOfFiniteTypeOver :
    BraidedCategory (LocallyOfFiniteTypeOver S) :=
  .ofCartesianMonoidalCategory

/-- The restriction of `F` to schemes locally of finite type over `S`, as a presheaf of
multiplicative commutative groups (Mathlib's `AddCommGrpCat.toCommGrp`). -/
def locallyOfFiniteTypeCommGrpFunctor : (LocallyOfFiniteTypeOver S)ᵒᵖ ⥤ CommGrpCat.{w} :=
  (locallyOfFiniteTypeOverInclusion S).op ⋙ F ⋙ AddCommGrpCat.toCommGrp

/-- The representation `e` restricted to schemes locally of finite type over `S`, for the
multiplicative presheaf `locallyOfFiniteTypeCommGrpFunctor F`. -/
def commGrpRepresentableBy :
    (locallyOfFiniteTypeCommGrpFunctor F ⋙ CategoryTheory.forget CommGrpCat).RepresentableBy
      P.toLocallyOfFiniteTypeOver where
  homEquiv := (representableByLocallyOfFiniteType e).homEquiv.trans Multiplicative.ofAdd
  homEquiv_comp f g := by
    change Multiplicative.ofAdd ((representableByLocallyOfFiniteType e).homEquiv (f ≫ g)) = _
    rw [(representableByLocallyOfFiniteType e).homEquiv_comp]
    rfl

theorem commGrpRepresentableBy_homEquiv {T : LocallyOfFiniteTypeOver S}
    (f : T ⟶ P.toLocallyOfFiniteTypeOver) :
    (commGrpRepresentableBy F P e).homEquiv f =
      Multiplicative.ofAdd
        (e.homEquiv ((LocallyOfFiniteTypeOver.toLocallyNoetherianOver S).map f)) :=
  rfl

/-- The commutative group object structure of `P` in schemes locally of finite type over `S`,
from the representation `e` (Mathlib's `CommGrpObj.ofRepresentableBy`). -/
@[instance_reducible]
def locallyOfFiniteTypeCommGrpObj : CommGrpObj P.toLocallyOfFiniteTypeOver :=
  CommGrpObj.ofRepresentableBy _ (locallyOfFiniteTypeCommGrpFunctor F)
    (commGrpRepresentableBy F P e)

/-- **The group law of a representing scheme.** For `S` locally Noetherian and a presheaf of
abelian groups `F` on `Over S` whose restriction to locally Noetherian test schemes is represented
by `P` locally of finite type over `S`, `P` is a commutative group object of `Over S`. -/
@[instance_reducible]
def commGrpObjOfRepresentableBy : CommGrpObj P.obj :=
  letI := locallyOfFiniteTypeCommGrpObj F P e
  CommGrpObj.ofFullSubcategory P.toLocallyOfFiniteTypeOver

open scoped CategoryTheory.MonObj

/-- The unit of `P` in schemes locally of finite type over `S` corresponds to `1`. -/
theorem locallyOfFiniteTypeCommGrpObj_one :
    letI := locallyOfFiniteTypeCommGrpObj F P e
    MonObj.one (X := P.toLocallyOfFiniteTypeOver) =
      (commGrpRepresentableBy F P e).homEquiv'.symm 1 :=
  rfl

/-- The multiplication of `P` in schemes locally of finite type over `S` corresponds to the
product of the two projections. -/
theorem locallyOfFiniteTypeCommGrpObj_mul :
    letI := locallyOfFiniteTypeCommGrpObj F P e
    MonObj.mul (X := P.toLocallyOfFiniteTypeOver) =
      (commGrpRepresentableBy F P e).homEquiv'.symm
        ((commGrpRepresentableBy F P e).homEquiv' (fst _ _) *
          (commGrpRepresentableBy F P e).homEquiv' (snd _ _)) :=
  rfl

/-- `e` sends the unit of the group `T ⟶ P` to `0`. -/
theorem homEquiv_one (T : LocallyNoetherianOver S) :
    letI := commGrpObjOfRepresentableBy F P e
    e.homEquiv (ObjectProperty.homMk (1 : T.obj ⟶ P.obj)) = (0 : F.obj (op T.obj)) := by
  let := commGrpObjOfRepresentableBy F P e
  let := locallyOfFiniteTypeCommGrpObj F P e
  let Q := P.toLocallyOfFiniteTypeOver
  let incl := LocallyOfFiniteTypeOver.toLocallyNoetherianOver S
  have h₁ : (ObjectProperty.homMk (1 : T.obj ⟶ P.obj) : T ⟶ P) =
      (ObjectProperty.homMk (toUnit T.obj) : T ⟶ incl.obj (𝟙_ _)) ≫
        incl.map (MonObj.one (X := Q)) :=
    rfl
  have h₂ : e.homEquiv (incl.map (MonObj.one (X := Q))) = (0 : F.obj (op (𝟙_ (Over S)))) :=
    Multiplicative.ofAdd.injective ((commGrpRepresentableBy F P e).homEquiv.apply_symm_apply 1)
  rw [h₁, e.homEquiv_comp, h₂]
  exact map_zero (F.map _).hom

/-- **`e` is additive**: it sends the product of `f, g : T ⟶ P` for the group law of `P` to the
sum of their classes in `F(T)`, for every locally Noetherian `S`-scheme `T`. The right side is
written with Mathlib's `RepresentableBy.homEquiv'`, which is `e.homEquiv` with values typed in the
abelian group `F(T)`. -/
theorem homEquiv_mul {T : LocallyNoetherianOver S} (f g : T.obj ⟶ P.obj) :
    letI := commGrpObjOfRepresentableBy F P e
    e.homEquiv (ObjectProperty.homMk (f * g)) =
      e.homEquiv' (F := (locallyNoetherianOverInclusion S).op ⋙ F) (ObjectProperty.homMk f) +
        e.homEquiv' (F := (locallyNoetherianOverInclusion S).op ⋙ F) (ObjectProperty.homMk g) := by
  let := commGrpObjOfRepresentableBy F P e
  let := locallyOfFiniteTypeCommGrpObj F P e
  let Q := P.toLocallyOfFiniteTypeOver
  let incl := LocallyOfFiniteTypeOver.toLocallyNoetherianOver S
  let a : T ⟶ incl.obj (Q ⊗ Q) := ObjectProperty.homMk (lift f g)
  have h₁ : (ObjectProperty.homMk (f * g) : T ⟶ P) = a ≫ incl.map (MonObj.mul (X := Q)) := rfl
  have h₂ : e.homEquiv' (F := (locallyNoetherianOverInclusion S).op ⋙ F)
      (incl.map (MonObj.mul (X := Q))) =
        e.homEquiv' (F := (locallyNoetherianOverInclusion S).op ⋙ F) (incl.map (fst Q Q)) +
          e.homEquiv' (F := (locallyNoetherianOverInclusion S).op ⋙ F) (incl.map (snd Q Q)) := by
    apply Multiplicative.ofAdd.injective
    rw [ofAdd_add, locallyOfFiniteTypeCommGrpObj_mul]
    exact (commGrpRepresentableBy F P e).homEquiv.apply_symm_apply _
  have h₃ (m : Q ⊗ Q ⟶ Q) :
      e.homEquiv' (F := (locallyNoetherianOverInclusion S).op ⋙ F) (a ≫ incl.map m) =
        (F.map (op (lift f g))).hom
          (e.homEquiv' (F := (locallyNoetherianOverInclusion S).op ⋙ F) (incl.map m)) :=
    e.homEquiv_comp _ _
  have h₄ : a ≫ incl.map (fst Q Q) = ObjectProperty.homMk f :=
    ObjectProperty.hom_ext _ (lift_fst f g)
  have h₅ : a ≫ incl.map (snd Q Q) = ObjectProperty.homMk g :=
    ObjectProperty.hom_ext _ (lift_snd f g)
  rw [h₁]
  refine (h₃ _).trans ?_
  rw [h₂, map_add, ← h₃, ← h₃, h₄, h₅]

/-- `e` sends the inverse for the group law of `P` to the negative. -/
theorem homEquiv_inv {T : LocallyNoetherianOver S} (f : T.obj ⟶ P.obj) :
    letI := commGrpObjOfRepresentableBy F P e
    e.homEquiv (ObjectProperty.homMk f⁻¹) =
      -e.homEquiv' (F := (locallyNoetherianOverInclusion S).op ⋙ F) (ObjectProperty.homMk f) := by
  let := commGrpObjOfRepresentableBy F P e
  have h : e.homEquiv' (F := (locallyNoetherianOverInclusion S).op ⋙ F)
      (ObjectProperty.homMk f⁻¹) +
        e.homEquiv' (F := (locallyNoetherianOverInclusion S).op ⋙ F) (ObjectProperty.homMk f) =
      0 := by
    rw [← homEquiv_mul, inv_mul_cancel]
    exact homEquiv_one F P e T
  have h' := eq_neg_of_add_eq_zero_left h
  exact h'

/-- **The representation as an isomorphism of abelian groups**: for every locally Noetherian
`S`-scheme `T`, `e` is an additive isomorphism from the group `T ⟶ P`, written additively, to
`F(T)`. -/
def homAddEquiv (T : LocallyNoetherianOver S) :
    letI := commGrpObjOfRepresentableBy F P e
    Additive (T.obj ⟶ P.obj) ≃+ F.obj (op T.obj) :=
  letI := commGrpObjOfRepresentableBy F P e
  AddEquiv.mk'
    (Additive.toMul.trans ((locallyNoetherianOver S).fullyFaithfulι.homEquiv.symm.trans e.homEquiv))
    fun a b => homEquiv_mul F P e a.toMul b.toMul

@[simp]
theorem homAddEquiv_apply (T : LocallyNoetherianOver S) (f : T.obj ⟶ P.obj) :
    letI := commGrpObjOfRepresentableBy F P e
    homAddEquiv F P e T (Additive.ofMul f) = e.homEquiv (ObjectProperty.homMk f) :=
  rfl

end AlgebraicGeometry.Scheme.LocallyNoetherianOver
