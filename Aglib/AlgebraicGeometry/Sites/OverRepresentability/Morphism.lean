/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.CommGrpObj
public import Mathlib.CategoryTheory.Yoneda

/-!
# Morphisms on the supplied locally Noetherian representatives

The map induced by a natural transformation uses Mathlib's fully faithful
Yoneda embedding and the original supplied representations. A native universe
lift keeps the arbitrary value universe of the existing group-law owner.
The whole Yoneda equation is proved before its formula on represented tests.
No second representing object or group structure is chosen.

For group compatibility, the base is locally Noetherian and the selected
representatives are locally of finite type. This ensures that the actual unit
and product are represented tests; products of arbitrary locally Noetherian
schemes are not assumed to be locally Noetherian.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe w u

namespace AlgebraicGeometry.Scheme.LocallyNoetherianOver

variable {S : Scheme.{u}}
  (F G H : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{w})
  (P Q U : LocallyNoetherianOver S)
  (eP : ((locallyNoetherianOverInclusion S).op ⋙ F ⋙
    CategoryTheory.forget AddCommGrpCat).RepresentableBy P)
  (eQ : ((locallyNoetherianOverInclusion S).op ⋙ G ⋙
    CategoryTheory.forget AddCommGrpCat).RepresentableBy Q)
  (eU : ((locallyNoetherianOverInclusion S).op ⋙ H ⋙
    CategoryTheory.forget AddCommGrpCat).RepresentableBy U)

/-- Mathlib's native universe-lifted Yoneda isomorphism for the ORIGINAL
representation. The representing object and represented elements stay fixed. -/
def representingYonedaIso :
    uliftYoneda.{w}.obj P ≅
      ((locallyNoetherianOverInclusion S).op ⋙ F ⋙
        CategoryTheory.forget AddCommGrpCat) ⋙ uliftFunctor.{u} :=
  (Functor.RepresentableBy.equivUliftYonedaIso _ P)
    (Functor.representableByUliftFunctorEquiv.symm eP)

/-- The original representative map is the preimage under the existing
fully faithful Yoneda embedding. There is no new Yoneda construction. -/
def representedMap (a : F ⟶ G) : P ⟶ Q :=
  (ULiftYoneda.fullyFaithful (LocallyNoetherianOver S)).preimage
    ((representingYonedaIso F P eP).hom ≫
      Functor.whiskerRight
        (Functor.whiskerLeft (locallyNoetherianOverInclusion S).op
          (Functor.whiskerRight a (CategoryTheory.forget AddCommGrpCat))) uliftFunctor.{u} ≫
      (representingYonedaIso G Q eQ).inv)

/-- The whole original represented square, before evaluation on any point. -/
theorem uliftYoneda_map_representedMap (a : F ⟶ G) :
    uliftYoneda.map (representedMap F G P Q eP eQ a) =
      (representingYonedaIso F P eP).hom ≫
        Functor.whiskerRight
          (Functor.whiskerLeft (locallyNoetherianOverInclusion S).op
            (Functor.whiskerRight a (CategoryTheory.forget AddCommGrpCat))) uliftFunctor.{u} ≫
        (representingYonedaIso G Q eQ).inv :=
  (ULiftYoneda.fullyFaithful (LocallyNoetherianOver S)).map_preimage _

/-- The original representations intertwine the whole Yoneda morphism. -/
@[reassoc]
theorem uliftYoneda_map_representedMap_comp (a : F ⟶ G) :
    uliftYoneda.map (representedMap F G P Q eP eQ a) ≫ (representingYonedaIso G Q eQ).hom =
      (representingYonedaIso F P eP).hom ≫
        Functor.whiskerRight
          (Functor.whiskerLeft (locallyNoetherianOverInclusion S).op
            (Functor.whiskerRight a (CategoryTheory.forget AddCommGrpCat))) uliftFunctor.{u} := by
  rw [uliftYoneda_map_representedMap]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Evaluation of the whole comparison on the original locally Noetherian
test category. The supplied representation, without its temporary lift,
gives exactly the original natural-transformation component. -/
theorem homEquiv_comp_representedMap (a : F ⟶ G)
    {T : LocallyNoetherianOver S} (f : T ⟶ P) :
    eQ.homEquiv (f ≫ representedMap F G P Q eP eQ a) =
      (a.app (op T.obj)).hom (eP.homEquiv f) := by
  have h := congrArg (fun q => (q.app (op T)) (ULift.up f))
    (uliftYoneda_map_representedMap_comp F G P Q eP eQ a)
  change ULift.up (eQ.homEquiv (f ≫ representedMap F G P Q eP eQ a)) =
    ULift.up ((a.app (op T.obj)).hom (eP.homEquiv f)) at h
  exact congrArg ULift.down h

/-- In particular, the original universal element classifies this same map. -/
theorem homEquiv_representedMap (a : F ⟶ G) :
    eQ.homEquiv (representedMap F G P Q eP eQ a) =
      (a.app (op P.obj)).hom (eP.homEquiv (𝟙 P)) := by
  simpa only [Category.id_comp] using homEquiv_comp_representedMap F G P Q eP eQ a (𝟙 P)

/-- Uniqueness is checked through the same supplied representation. -/
theorem representedMap_unique (a : F ⟶ G) (f : P ⟶ Q)
    (hf : eQ.homEquiv f = (a.app (op P.obj)).hom (eP.homEquiv (𝟙 P))) :
    f = representedMap F G P Q eP eQ a :=
  eQ.homEquiv.injective (hf.trans (homEquiv_representedMap F G P Q eP eQ a).symm)

/-- Identity on the presheaf gives the identity of its original representative. -/
@[simp]
theorem representedMap_id : representedMap F F P P eP eP (𝟙 F) = 𝟙 P := by
  apply eP.homEquiv.injective
  rw [homEquiv_representedMap]
  rfl

/-- Composition is preserved without changing any of the supplied representatives. -/
theorem representedMap_comp (a : F ⟶ G) (b : G ⟶ H) :
    representedMap F H P U eP eU (a ≫ b) =
      representedMap F G P Q eP eQ a ≫ representedMap G H Q U eQ eU b := by
  apply eU.homEquiv.injective
  rw [homEquiv_representedMap, homEquiv_comp_representedMap, homEquiv_representedMap]
  rfl

/-- The original universal sheaf sections satisfy the represented-map
equation. Their definition only evaluates the supplied representations at
their original locally Noetherian representing objects. -/
theorem universalClass_representedMap (a : F ⟶ G) :
    (G.map (representedMap F G P Q eP eQ a).hom.op).hom (eQ.homEquiv (𝟙 Q)) =
      (a.app (op P.obj)).hom (eP.homEquiv (𝟙 P)) :=
  (eQ.homEquiv_eq _).symm.trans (homEquiv_representedMap F G P Q eP eQ a)

/-- The whole original universal-class equation on EVERY test scheme. This
uses presheaf naturality after the represented map is constructed, and does
not assert representability outside the locally Noetherian test category. -/
theorem universalClass_comp_representedMap (a : F ⟶ G)
    {T : Over S} (f : T ⟶ P.obj) :
    (G.map (f ≫ (representedMap F G P Q eP eQ a).hom).op).hom (eQ.homEquiv (𝟙 Q)) =
      (a.app (op T)).hom ((F.map f.op).hom (eP.homEquiv (𝟙 P))) := by
  rw [op_comp, G.map_comp]
  change (G.map f.op).hom
    ((G.map (representedMap F G P Q eP eQ a).hom.op).hom (eQ.homEquiv (𝟙 Q))) = _
  rw [universalClass_representedMap]
  exact (congrArg (fun q => q.hom (eP.homEquiv (𝟙 P))) (a.naturality f.op)).symm

section GroupLaw

variable [IsLocallyNoetherian S]
  [LocallyOfFiniteType P.obj.hom] [LocallyOfFiniteType Q.obj.hom]

set_option backward.isDefEq.respectTransparency false in
/-- The original representative map sends the original unit-valued point to
the original unit-valued point on every represented test. -/
theorem representedMap_one (a : F ⟶ G) (T : LocallyNoetherianOver S) :
    letI := commGrpObjOfRepresentableBy F P eP
    letI := commGrpObjOfRepresentableBy G Q eQ
    (1 : T.obj ⟶ P.obj) ≫ (representedMap F G P Q eP eQ a).hom = 1 := by
  let := commGrpObjOfRepresentableBy F P eP
  let := commGrpObjOfRepresentableBy G Q eQ
  have h : (ObjectProperty.homMk ((1 : T.obj ⟶ P.obj) ≫
      (representedMap F G P Q eP eQ a).hom) : T ⟶ Q) = ObjectProperty.homMk 1 := by
    apply eQ.homEquiv.injective
    change eQ.homEquiv ((ObjectProperty.homMk (1 : T.obj ⟶ P.obj) : T ⟶ P) ≫
      representedMap F G P Q eP eQ a) = _
    rw [homEquiv_comp_representedMap, homEquiv_one, homEquiv_one, map_zero]
  exact congrArg (fun q : T ⟶ Q => q.hom) h

set_option backward.isDefEq.respectTransparency false in
/-- The original representative map carries products to products on the
represented test category because the original presheaf morphism is additive. -/
theorem representedMap_mul (a : F ⟶ G) {T : LocallyNoetherianOver S}
    (f g : T.obj ⟶ P.obj) :
    letI := commGrpObjOfRepresentableBy F P eP
    letI := commGrpObjOfRepresentableBy G Q eQ
    (f * g) ≫ (representedMap F G P Q eP eQ a).hom =
      (f ≫ (representedMap F G P Q eP eQ a).hom) *
        (g ≫ (representedMap F G P Q eP eQ a).hom) := by
  let := commGrpObjOfRepresentableBy F P eP
  let := commGrpObjOfRepresentableBy G Q eQ
  have h : (ObjectProperty.homMk ((f * g) ≫
      (representedMap F G P Q eP eQ a).hom) : T ⟶ Q) =
      ObjectProperty.homMk ((f ≫ (representedMap F G P Q eP eQ a).hom) *
        (g ≫ (representedMap F G P Q eP eQ a).hom)) := by
    apply eQ.homEquiv.injective
    change eQ.homEquiv ((ObjectProperty.homMk (f * g) : T ⟶ P) ≫
      representedMap F G P Q eP eQ a) = _
    rw [homEquiv_comp_representedMap, homEquiv_mul, homEquiv_mul, map_add]
    exact congrArg₂ (fun x y : G.obj (op T.obj) => x + y)
      (homEquiv_comp_representedMap F G P Q eP eQ a (ObjectProperty.homMk f)).symm
      (homEquiv_comp_representedMap F G P Q eP eQ a (ObjectProperty.homMk g)).symm
  exact congrArg (fun q : T ⟶ Q => q.hom) h

set_option backward.isDefEq.respectTransparency false in
/-- The same underlying map preserves the selected group structures. The
actual unit and product are legitimate locally Noetherian tests by local
finite type; no closure of all locally Noetherian schemes under products is used. -/
theorem isMonHom_representedMap (a : F ⟶ G) :
    letI := commGrpObjOfRepresentableBy F P eP
    letI := commGrpObjOfRepresentableBy G Q eQ
    IsMonHom (representedMap F G P Q eP eQ a).hom := by
  let := commGrpObjOfRepresentableBy F P eP
  let := commGrpObjOfRepresentableBy G Q eQ
  constructor
  · let T : LocallyNoetherianOver S :=
      ⟨𝟙_ (Over S), by change IsLocallyNoetherian S; infer_instance⟩
    have h := representedMap_one F G P Q eP eQ a T
    simp only [CategoryTheory.Hom.one_def] at h
    dsimp only [T] at h
    have ht : toUnit (𝟙_ (Over S)) = 𝟙 (𝟙_ (Over S)) := toUnit_unique _ _
    simpa only [ht, Category.id_comp] using h
  · let T : LocallyNoetherianOver S :=
      ⟨P.obj ⊗ P.obj, LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst P.obj.hom P.obj.hom ≫ P.obj.hom)⟩
    have h := representedMap_mul F G P Q eP eQ a (T := T) (fst P.obj P.obj) (snd P.obj P.obj)
    simp only [CategoryTheory.Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [← lift_map, lift_fst_snd, Category.id_comp] at h
    exact h

end GroupLaw

end AlgebraicGeometry.Scheme.LocallyNoetherianOver
