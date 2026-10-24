/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyNoetherianOver
public import Aglib.CategoryTheory.ObjectProperty.RepresentableBy
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Schemes locally of finite type over a base

For a scheme `S`, `Scheme.locallyOfFiniteTypeOver S` is the property of an object `T ⟶ S` of
`Over S` that the structure morphism is locally of finite type, and
`Scheme.LocallyOfFiniteTypeOver S` is its full subcategory, with all morphisms over `S`.

* The property is closed under isomorphisms, under the terminal object `𝟙 S`
  (`Scheme.isClosedUnderLimitsOfShape_discrete_pEmpty_locallyOfFiniteTypeOver`) and under binary
  products (`Scheme.isClosedUnderBinaryProducts_locallyOfFiniteTypeOver`): a product of `Y ⟶ S` and
  `Z ⟶ S` in `Over S` is isomorphic to `Y ×_S Z ⟶ Y ⟶ S`, which is locally of finite type by
  base change and composition. Hence Mathlib's `CartesianMonoidalCategory.fullSubcategory`
  makes `Scheme.LocallyOfFiniteTypeOver S` a cartesian monoidal category whose products are the
  fibre products over `S`.
* For `S` locally Noetherian, every scheme locally of finite type over `S` is locally Noetherian
  (Stacks, Tag 01T6; Mathlib's `LocallyOfFiniteType.isLocallyNoetherian`):
  `Scheme.locallyOfFiniteTypeOver_le_locallyNoetherianOver`, with the inclusion
  `Scheme.LocallyOfFiniteTypeOver.toLocallyNoetherianOver` of full subcategories.
* A presheaf on locally Noetherian test schemes over `S` represented by a scheme locally of
  finite type over `S` is represented by the same scheme on test schemes locally of finite type
  (`Scheme.LocallyNoetherianOver.representableByLocallyOfFiniteType`).

Unlike locally Noetherian schemes over `S`, schemes locally of finite type over `S` are closed
under fibre products over `S`. This is why group laws of schemes representing functors on locally
Noetherian test schemes are built in this full subcategory
(`Aglib.AlgebraicGeometry.Sites.OverRepresentability.CommGrpObj`).
-/

@[expose] public section

noncomputable section

universe w u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry.Scheme

/-- The property of an object `T ⟶ S` of `Over S` that the structure morphism is locally of
finite type. It is Mathlib's `MorphismProperty.overObj @LocallyOfFiniteType`
(`locallyOfFiniteTypeOver_eq_overObj`). -/
abbrev locallyOfFiniteTypeOver (S : Scheme.{u}) : ObjectProperty (Over S) :=
  fun T => LocallyOfFiniteType T.hom

theorem locallyOfFiniteTypeOver_eq_overObj (S : Scheme.{u}) :
    locallyOfFiniteTypeOver S = MorphismProperty.overObj (X := S) @LocallyOfFiniteType :=
  rfl

/-- **Schemes locally of finite type over `S`**: the full subcategory of `Over S` on the objects
`T ⟶ S` locally of finite type, with all morphisms over `S`. -/
abbrev LocallyOfFiniteTypeOver (S : Scheme.{u}) := (locallyOfFiniteTypeOver S).FullSubcategory

/-- The structure morphism of an object of `LocallyOfFiniteTypeOver S` is locally of finite
type. -/
instance LocallyOfFiniteTypeOver.locallyOfFiniteType {S : Scheme.{u}}
    (T : LocallyOfFiniteTypeOver S) : LocallyOfFiniteType T.obj.hom :=
  T.property

/-- The inclusion of schemes locally of finite type over `S` into `Over S`. -/
abbrev locallyOfFiniteTypeOverInclusion (S : Scheme.{u}) : LocallyOfFiniteTypeOver S ⥤ Over S :=
  (locallyOfFiniteTypeOver S).ι

variable {S : Scheme.{u}}

/-- Being locally of finite type over `S` is invariant under isomorphisms in `Over S`. -/
instance isClosedUnderIsomorphisms_locallyOfFiniteTypeOver :
    (locallyOfFiniteTypeOver S).IsClosedUnderIsomorphisms where
  of_iso {X Y} e (_ : LocallyOfFiniteType X.hom) := by
    change LocallyOfFiniteType Y.hom
    have : IsIso e.inv.left := (Over.forget S).map_isIso e.inv
    have : LocallyOfFiniteType e.inv.left := inferInstance
    rw [← Over.w e.inv]
    infer_instance

/-- **The terminal object**: a terminal object of `Over S`, isomorphic to `𝟙 S`, is locally of
finite type over `S`. -/
instance isClosedUnderLimitsOfShape_discrete_pEmpty_locallyOfFiniteTypeOver :
    (locallyOfFiniteTypeOver S).IsClosedUnderLimitsOfShape (Discrete PEmpty.{1}) where
  limitsOfShape_le X := by
    rintro ⟨h⟩
    have hX : IsTerminal X :=
      (IsLimit.equivOfNatIsoOfIso h.diag.uniqueFromEmpty _ _
        (by exact Cone.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩))).1 h.isLimit
    refine (locallyOfFiniteTypeOver S).prop_of_iso (hX.uniqueUpToIso Over.mkIdTerminal).symm ?_
    change LocallyOfFiniteType (𝟙 S)
    infer_instance

/-- **Binary products of schemes locally of finite type over `S`**: the apex of a limiting
binary fan in `Over S` of two objects locally of finite type over `S` is locally of finite type
over `S`. It is isomorphic to `Y ×_S Z ⟶ Y ⟶ S`, locally of finite type by base change and
composition. -/
instance isClosedUnderBinaryProducts_locallyOfFiniteTypeOver :
    (locallyOfFiniteTypeOver S).IsClosedUnderLimitsOfShape (Discrete WalkingPair) where
  limitsOfShape_le X := by
    rintro ⟨h⟩
    have h₁ : LocallyOfFiniteType (h.diag.obj ⟨WalkingPair.left⟩).hom := h.prop_diag_obj _
    have h₂ : LocallyOfFiniteType (h.diag.obj ⟨WalkingPair.right⟩).hom := h.prop_diag_obj _
    have e : X ≅ h.diag.obj ⟨WalkingPair.left⟩ ⊗ h.diag.obj ⟨WalkingPair.right⟩ :=
      IsLimit.conePointsIsoOfNatIso h.isLimit (tensorProductIsBinaryProduct _ _)
        (diagramIsoPair h.diag)
    refine (locallyOfFiniteTypeOver S).prop_of_iso e.symm ?_
    change LocallyOfFiniteType (pullback.fst _ _ ≫ _)
    infer_instance

/-- **Schemes locally of finite type over a locally Noetherian base are locally Noetherian**
(Stacks, Tag 01T6; Mathlib's `LocallyOfFiniteType.isLocallyNoetherian`). -/
theorem locallyOfFiniteTypeOver_le_locallyNoetherianOver (S : Scheme.{u}) [IsLocallyNoetherian S] :
    locallyOfFiniteTypeOver S ≤ locallyNoetherianOver S := fun T (_ : LocallyOfFiniteType T.hom) =>
  LocallyOfFiniteType.isLocallyNoetherian T.hom

/-- The inclusion of schemes locally of finite type over a locally Noetherian `S` into locally
Noetherian schemes over `S`. -/
abbrev LocallyOfFiniteTypeOver.toLocallyNoetherianOver (S : Scheme.{u}) [IsLocallyNoetherian S] :
    LocallyOfFiniteTypeOver S ⥤ LocallyNoetherianOver S :=
  ObjectProperty.ιOfLE (locallyOfFiniteTypeOver_le_locallyNoetherianOver S)

/-- A locally Noetherian scheme over `S` locally of finite type over `S`, as an object of
`LocallyOfFiniteTypeOver S`. -/
abbrev LocallyNoetherianOver.toLocallyOfFiniteTypeOver (P : LocallyNoetherianOver S)
    [LocallyOfFiniteType P.obj.hom] : LocallyOfFiniteTypeOver S :=
  ⟨P.obj, ‹LocallyOfFiniteType P.obj.hom›⟩

/-- **A representation on locally Noetherian test schemes by a scheme locally of finite type
restricts to test schemes locally of finite type.** For `S` locally Noetherian and a presheaf
`F` on locally Noetherian schemes over `S` represented by `P` with `P ⟶ S` locally of finite
type, `F` restricted to schemes locally of finite type over `S` is represented by `P`. -/
def LocallyNoetherianOver.representableByLocallyOfFiniteType [IsLocallyNoetherian S]
    {F : (LocallyNoetherianOver S)ᵒᵖ ⥤ Type w} {P : LocallyNoetherianOver S}
    [LocallyOfFiniteType P.obj.hom] (e : F.RepresentableBy P) :
    ((LocallyOfFiniteTypeOver.toLocallyNoetherianOver S).op ⋙ F).RepresentableBy
      P.toLocallyOfFiniteTypeOver :=
  ObjectProperty.representableByιOfLE _ e

theorem LocallyNoetherianOver.representableByLocallyOfFiniteType_homEquiv [IsLocallyNoetherian S]
    {F : (LocallyNoetherianOver S)ᵒᵖ ⥤ Type w} {P : LocallyNoetherianOver S}
    [LocallyOfFiniteType P.obj.hom] (e : F.RepresentableBy P) {T : LocallyOfFiniteTypeOver S}
    (f : T ⟶ P.toLocallyOfFiniteTypeOver) :
    (representableByLocallyOfFiniteType e).homEquiv f = e.homEquiv (ObjectProperty.homMk f.hom) :=
  rfl

end AlgebraicGeometry.Scheme
