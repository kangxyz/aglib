/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.BaseChange

/-!
# Contravariant Picard pullback for the original source morphism

For an arbitrary morphism `f : X ⟶ Y` over a base scheme, the original family
map is `(Over.pullback T.hom).map f`. Its additive line-bundle pullback descends
through the original quotient by base classes and then through the existing
fppf sheafification. Identity, composition and the whole original class
equations are proved before any representing scheme is chosen.

The source morphism need not be flat or smooth. No origins, properness,
Noetherianity or reducedness assumptions occur in these operations.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local

variable {S : Scheme.{u}} {X Y Z : Over S}

/-- The original map on the literal fibre-product families. -/
def familyMapOfHom (f : X ⟶ Y) (T : Over S) :
    pullback X.hom T.hom ⟶ pullback Y.hom T.hom :=
  ((Over.pullback T.hom).map f).left

set_option backward.isDefEq.respectTransparency false in
/-- The first projection records the original source morphism. -/
@[reassoc (attr := simp)]
theorem familyMapOfHom_fst (f : X ⟶ Y) (T : Over S) :
    familyMapOfHom f T ≫ pullback.fst Y.hom T.hom =
      pullback.fst X.hom T.hom ≫ f.left :=
  pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The original parameter projection is unchanged. -/
@[reassoc (attr := simp)]
theorem familyMapOfHom_snd (f : X ⟶ Y) (T : Over S) :
    familyMapOfHom f T ≫ pullback.snd Y.hom T.hom = pullback.snd X.hom T.hom :=
  pullback.lift_snd _ _ _

/-- Identity on the source gives the original identity on every family. -/
@[simp]
theorem familyMapOfHom_id (X : Over S) (T : Over S) :
    familyMapOfHom (𝟙 X) T = 𝟙 (pullback X.hom T.hom) :=
  congrArg (fun q => q.left) ((Over.pullback T.hom).map_id X)

/-- Source composition uses the same actual family maps. -/
theorem familyMapOfHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) (T : Over S) :
    familyMapOfHom (f ≫ g) T = familyMapOfHom f T ≫ familyMapOfHom g T :=
  congrArg (fun q => q.left) ((Over.pullback T.hom).map_comp f g)

set_option backward.isDefEq.respectTransparency false in
/-- The whole source-family map commutes with every original parameter map. -/
@[reassoc]
theorem familyMapOfHom_naturality (f : X ⟶ Y) {T T' : Over S} (g : T' ⟶ T) :
    (familyScheme X.hom).map g ≫ familyMapOfHom f T =
      familyMapOfHom f T' ≫ (familyScheme Y.hom).map g := by
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- Source pullback before passing to Picard classes, as a whole natural map. -/
def familyMapOfHomNat (f : X ⟶ Y) : familyScheme X.hom ⟶ familyScheme Y.hom where
  app T := familyMapOfHom f T
  naturality _ _ g := familyMapOfHom_naturality f g

/-- Additive pullback on the existing family Picard presheaves. -/
def familyPicardPullback (f : X ⟶ Y) :
    familyPicardFunctor Y.hom ⟶ familyPicardFunctor X.hom :=
  Functor.whiskerRight (NatTrans.op (familyMapOfHomNat f)) picardFunctor

/-- The family operation is the original line-bundle pullback on every test. -/
theorem familyPicardPullback_app_apply (f : X ⟶ Y) (T : (Over S)ᵒᵖ)
    (a : PicardGroup (pullback Y.hom T.unop.hom)) :
    ((familyPicardPullback f).app T).hom a = pullbackClass (familyMapOfHom f T.unop) a :=
  rfl

/-- The whole additive family pullback has the identity law. -/
@[simp]
theorem familyPicardPullback_id (X : Over S) :
    familyPicardPullback (𝟙 X) = 𝟙 (familyPicardFunctor X.hom) := by
  ext T a
  change PicardGroup (pullback X.hom T.unop.hom) at a
  change pullbackClass (familyMapOfHom (𝟙 X) T.unop) a = a
  rw [familyMapOfHom_id, pullbackClass_id]

/-- The family Picard operation is contravariant in the original source. -/
theorem familyPicardPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    familyPicardPullback (f ≫ g) = familyPicardPullback g ≫ familyPicardPullback f := by
  ext T a
  change PicardGroup (pullback Z.hom T.unop.hom) at a
  change pullbackClass (familyMapOfHom (f ≫ g) T.unop) a =
    pullbackClass (familyMapOfHom f T.unop) (pullbackClass (familyMapOfHom g T.unop) a)
  rw [familyMapOfHom_comp, pullbackClass_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The pullback of an original base class is that same original base class. -/
theorem familyPicardPullback_basePullback (f : X ⟶ Y) (T : (Over S)ᵒᵖ)
    (a : PicardGroup T.unop.left) :
    ((familyPicardPullback f).app T).hom (((basePullback Y.hom).app T).hom a) =
      ((basePullback X.hom).app T).hom a := by
  change pullbackClass (familyMapOfHom f T.unop)
    (pullbackClass (pullback.snd Y.hom T.unop.hom) a) =
      pullbackClass (pullback.snd X.hom T.unop.hom) a
  rw [← pullbackClass_comp, familyMapOfHom_snd]

/-- Whole compatibility with the original base-pullback natural transformation. -/
theorem basePullback_comp_familyPicardPullback (f : X ⟶ Y) :
    basePullback Y.hom ≫ familyPicardPullback f = basePullback X.hom := by
  ext T a
  exact familyPicardPullback_basePullback f T a

/-- The existing subgroup of base classes is preserved; no origin is needed. -/
theorem baseImage_le_comap_familyPicardPullback (f : X ⟶ Y) (T : (Over S)ᵒᵖ) :
    baseImage Y.hom T ≤ (baseImage X.hom T).comap ((familyPicardPullback f).app T).hom := by
  rintro _ ⟨a, rfl⟩
  exact ⟨a, (familyPicardPullback_basePullback f T a).symm⟩

/-- Contravariant pullback on the original relative Picard quotient presheaf. -/
def relativePicardPullback (f : X ⟶ Y) :
    relativePicardFunctor Y.hom ⟶ relativePicardFunctor X.hom where
  app T := AddCommGrpCat.ofHom
    (QuotientAddGroup.map _ _ ((familyPicardPullback f).app T).hom
      (baseImage_le_comap_familyPicardPullback f T))
  naturality T T' g := by
    ext a
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
    change QuotientAddGroup.mk
        (((familyPicardPullback f).app T').hom (((familyPicardFunctor Y.hom).map g).hom a)) =
      QuotientAddGroup.mk
        (((familyPicardFunctor X.hom).map g).hom (((familyPicardPullback f).app T).hom a))
    exact congrArg QuotientAddGroup.mk
      (congrArg (fun q => q.hom a) ((familyPicardPullback f).naturality g))

/-- The quotient operation retains its original class formula. -/
theorem relativePicardPullback_app_mk (f : X ⟶ Y) (T : (Over S)ᵒᵖ)
    (a : PicardGroup (pullback Y.hom T.unop.hom)) :
    ((relativePicardPullback f).app T).hom (QuotientAddGroup.mk a) =
      QuotientAddGroup.mk (pullbackClass (familyMapOfHom f T.unop) a) := rfl

/-- Pullback commutes with the original quotient projection on all tests. -/
theorem familyPicardPullback_comp_quotientProjection (f : X ⟶ Y) :
    familyPicardPullback f ≫ quotientProjection X.hom =
      quotientProjection Y.hom ≫ relativePicardPullback f := by
  ext T a
  rfl

/-- Identity for the original relative Picard pullback. -/
@[simp]
theorem relativePicardPullback_id (X : Over S) :
    relativePicardPullback (𝟙 X) = 𝟙 (relativePicardFunctor X.hom) := by
  ext T a
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
  change PicardGroup (pullback X.hom T.unop.hom) at a
  change QuotientAddGroup.mk (pullbackClass (familyMapOfHom (𝟙 X) T.unop) a) =
    QuotientAddGroup.mk a
  rw [familyMapOfHom_id, pullbackClass_id]

/-- Contravariant composition for the original relative Picard pullback. -/
theorem relativePicardPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    relativePicardPullback (f ≫ g) = relativePicardPullback g ≫ relativePicardPullback f := by
  ext T a
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
  change PicardGroup (pullback Z.hom T.unop.hom) at a
  change QuotientAddGroup.mk (pullbackClass (familyMapOfHom (f ≫ g) T.unop) a) =
    QuotientAddGroup.mk (pullbackClass (familyMapOfHom f T.unop)
      (pullbackClass (familyMapOfHom g T.unop) a))
  rw [familyMapOfHom_comp, pullbackClass_comp]

/-- The fppf Picard pullback is the original sheafification of the whole
relative presheaf morphism. It requires no flatness of the source morphism. -/
def fppfPicardPullback (f : X ⟶ Y) : fppfPicardSheaf Y.hom ⟶ fppfPicardSheaf X.hom :=
  (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).map
    (relativePicardPullback f)

/-- The original sheafification unit intertwines source pullback. -/
@[reassoc]
theorem relativePicardPullback_comp_toFppfPicardSheaf (f : X ⟶ Y) :
    relativePicardPullback f ≫ toFppfPicardSheaf X.hom =
      toFppfPicardSheaf Y.hom ≫ (fppfPicardPullback f).hom :=
  toSheafify_naturality (Scheme.fppfTopology.over S) (relativePicardPullback f)

/-- The whole classifying-unit equation starts with the original family
Picard classes, before any represented test is evaluated. -/
theorem familyPicardPullback_comp_fppfClass (f : X ⟶ Y) :
    familyPicardPullback f ≫ quotientProjection X.hom ≫ toFppfPicardSheaf X.hom =
      quotientProjection Y.hom ≫ toFppfPicardSheaf Y.hom ≫ (fppfPicardPullback f).hom := by
  rw [← Category.assoc, familyPicardPullback_comp_quotientProjection,
    Category.assoc, relativePicardPullback_comp_toFppfPicardSheaf]

/-- The original fppf class equation on every test scheme and every line-bundle class. -/
theorem fppfPicardPullback_class (f : X ⟶ Y) (T : Over S)
    (a : PicardGroup (pullback Y.hom T.hom)) :
    ((quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T)).hom
        (pullbackClass (familyMapOfHom f T) a) =
      ((fppfPicardPullback f).hom.app (op T)).hom
        (((quotientProjection Y.hom ≫ toFppfPicardSheaf Y.hom).app (op T)).hom a) :=
  congrArg (fun q => q.hom a) (congr_app (familyPicardPullback_comp_fppfClass f) (op T))

/-- Identity for the same fppf Picard sheaf operation. -/
@[simp]
theorem fppfPicardPullback_id (X : Over S) :
    fppfPicardPullback (𝟙 X) = 𝟙 (fppfPicardSheaf X.hom) := by
  unfold fppfPicardPullback
  rw [relativePicardPullback_id]
  exact (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).map_id _

/-- Contravariant composition for the same original fppf sheaf operation. -/
theorem fppfPicardPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    fppfPicardPullback (f ≫ g) = fppfPicardPullback g ≫ fppfPicardPullback f := by
  unfold fppfPicardPullback
  rw [relativePicardPullback_comp]
  exact (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).map_comp _ _

section BaseChange

variable {S' : Scheme.{u}} (f : X ⟶ Y) (b : S' ⟶ S)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Source pullback commutes with the original pasted-pullback comparison,
as a whole scheme-map equation before passage to classes. -/
@[reassoc]
theorem familyMapOfHom_baseChange (T : Over S') :
    familyMapOfHom ((Over.pullback b).map f) T ≫ (familyBaseChangeIso Y.hom b T).hom =
      (familyBaseChangeIso X.hom b T).hom ≫ familyMapOfHom f ((Over.map b).obj T) := by
  have hf : ((Over.pullback b).map f).left ≫ pullback.fst Y.hom b =
      pullback.fst X.hom b ≫ f.left := pullback.lift_fst _ _ _
  have hl₁ : familyMapOfHom ((Over.pullback b).map f) T ≫
      pullback.fst (pullback.snd Y.hom b) T.hom =
        pullback.fst (pullback.snd X.hom b) T.hom ≫ ((Over.pullback b).map f).left := by
    simpa only [Over.pullback_obj_hom] using familyMapOfHom_fst ((Over.pullback b).map f) T
  have hl₂ : familyMapOfHom ((Over.pullback b).map f) T ≫
      pullback.snd (pullback.snd Y.hom b) T.hom =
        pullback.snd (pullback.snd X.hom b) T.hom := by
    simpa only [Over.pullback_obj_hom] using familyMapOfHom_snd ((Over.pullback b).map f) T
  have hr₁ : familyMapOfHom f ((Over.map b).obj T) ≫
      pullback.fst Y.hom (T.hom ≫ b) = pullback.fst X.hom (T.hom ≫ b) ≫ f.left := by
    simpa only [Over.map_obj_hom] using familyMapOfHom_fst f ((Over.map b).obj T)
  have hr₂ : familyMapOfHom f ((Over.map b).obj T) ≫
      pullback.snd Y.hom (T.hom ≫ b) = pullback.snd X.hom (T.hom ≫ b) := by
    simpa only [Over.map_obj_hom] using familyMapOfHom_snd f ((Over.map b).obj T)
  apply pullback.hom_ext
  · simp only [Category.assoc, familyBaseChangeIso_hom_fst]
    rw [reassoc_of% hl₁, hf, hr₁,
      familyBaseChangeIso_hom_fst_assoc X.hom b T]
  · simp only [Category.assoc, familyBaseChangeIso_hom_snd]
    rw [hl₂, hr₂, familyBaseChangeIso_hom_snd X.hom b T]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse comparison gives the same original source-family square. -/
@[reassoc]
theorem familyMapOfHom_baseChange_inv (T : Over S') :
    (familyBaseChangeIso X.hom b T).inv ≫ familyMapOfHom ((Over.pullback b).map f) T =
      familyMapOfHom f ((Over.map b).obj T) ≫ (familyBaseChangeIso Y.hom b T).inv := by
  apply (cancel_epi (familyBaseChangeIso X.hom b T).hom).mp
  apply (cancel_mono (familyBaseChangeIso Y.hom b T).hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using familyMapOfHom_baseChange f b T

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Whole base-change compatibility on the original family Picard presheaves. -/
@[reassoc]
theorem familyPicardPullback_baseChange :
    familyPicardPullback ((Over.pullback b).map f) ≫
        (familyPicardFunctorBaseChangeIso X.hom b).hom =
      (familyPicardFunctorBaseChangeIso Y.hom b).hom ≫
        Functor.whiskerLeft (Over.map b).op (familyPicardPullback f) := by
  ext T a
  change PicardGroup (pullback (pullback.snd Y.hom b) T.unop.hom) at a
  change pullbackClass (familyBaseChangeIso X.hom b T.unop).inv
      (pullbackClass (familyMapOfHom ((Over.pullback b).map f) T.unop) a) =
    pullbackClass (familyMapOfHom f ((Over.map b).obj T.unop))
      (pullbackClass (familyBaseChangeIso Y.hom b T.unop).inv a)
  rw [← pullbackClass_comp, ← pullbackClass_comp, familyMapOfHom_baseChange_inv]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original relative quotient comparison intertwines source pullback. -/
@[reassoc]
theorem relativePicardPullback_baseChange :
    relativePicardPullback ((Over.pullback b).map f) ≫
        (relativePicardFunctorBaseChangeIso X.hom b).hom =
      (relativePicardFunctorBaseChangeIso Y.hom b).hom ≫
        Functor.whiskerLeft (Over.map b).op (relativePicardPullback f) := by
  ext T a
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
  exact congrArg QuotientAddGroup.mk
    (congrArg (fun q => (q.app T).hom a) (familyPicardPullback_baseChange f b))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Source pullback commutes with the original fppf sheaf base-change
isomorphism on all tests. Its proof uses the original sheafification units. -/
@[reassoc]
theorem fppfPicardPullback_baseChange :
    (fppfPicardPullback ((Over.pullback b).map f)).hom ≫
        (fppfPicardSheafBaseChangeIso X.hom b).hom =
      (fppfPicardSheafBaseChangeIso Y.hom b).hom ≫
        Functor.whiskerLeft (Over.map b).op (fppfPicardPullback f).hom := by
  let push := (Over.map b).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)
  have hs : fppfPicardPullback ((Over.pullback b).map f) ≫
        (fppfPicardSheafBaseChangeSheafIso X.hom b).hom =
      (fppfPicardSheafBaseChangeSheafIso Y.hom b).hom ≫
        push.map (fppfPicardPullback f) := by
    apply (fppfPicardSheafHomEquiv (pullback.snd Y.hom b)
      (push.obj (fppfPicardSheaf X.hom))).injective
    change toFppfPicardSheaf (pullback.snd Y.hom b) ≫
        (fppfPicardPullback ((Over.pullback b).map f)).hom ≫
        (fppfPicardSheafBaseChangeIso X.hom b).hom =
      toFppfPicardSheaf (pullback.snd Y.hom b) ≫
        (fppfPicardSheafBaseChangeIso Y.hom b).hom ≫
        Functor.whiskerLeft (Over.map b).op (fppfPicardPullback f).hom
    calc
      _ = relativePicardPullback ((Over.pullback b).map f) ≫
          toFppfPicardSheaf (pullback.snd X.hom b) ≫
          (fppfPicardSheafBaseChangeIso X.hom b).hom := by
            exact (relativePicardPullback_comp_toFppfPicardSheaf_assoc
              ((Over.pullback b).map f) (fppfPicardSheafBaseChangeIso X.hom b).hom).symm
      _ = relativePicardPullback ((Over.pullback b).map f) ≫
          (relativePicardFunctorBaseChangeIso X.hom b).hom ≫
          Functor.whiskerLeft (Over.map b).op (toFppfPicardSheaf X.hom) := by
            rw [toFppfPicardSheaf_comp_fppfPicardSheafBaseChangeIso_hom]
      _ = (relativePicardFunctorBaseChangeIso Y.hom b).hom ≫
          Functor.whiskerLeft (Over.map b).op (relativePicardPullback f) ≫
          Functor.whiskerLeft (Over.map b).op (toFppfPicardSheaf X.hom) := by
            rw [← Category.assoc, relativePicardPullback_baseChange, Category.assoc]
      _ = (relativePicardFunctorBaseChangeIso Y.hom b).hom ≫
          Functor.whiskerLeft (Over.map b).op
            (relativePicardPullback f ≫ toFppfPicardSheaf X.hom) := by
            rw [Functor.whiskerLeft_comp]
      _ = (relativePicardFunctorBaseChangeIso Y.hom b).hom ≫
          Functor.whiskerLeft (Over.map b).op
            (toFppfPicardSheaf Y.hom ≫ (fppfPicardPullback f).hom) := by
            rw [relativePicardPullback_comp_toFppfPicardSheaf]
      _ = (relativePicardFunctorBaseChangeIso Y.hom b).hom ≫
          Functor.whiskerLeft (Over.map b).op (toFppfPicardSheaf Y.hom) ≫
          Functor.whiskerLeft (Over.map b).op (fppfPicardPullback f).hom := by
            rw [Functor.whiskerLeft_comp]
      _ = _ := by rw [toFppfPicardSheaf_comp_fppfPicardSheafBaseChangeIso_hom_assoc]
  exact congrArg (fun q => q.hom) hs

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse original sheaf comparison satisfies the same whole
source-pullback square, on arbitrary parameter schemes. -/
@[reassoc]
theorem fppfPicardPullback_baseChange_inv :
    (fppfPicardSheafBaseChangeIso Y.hom b).inv ≫
        (fppfPicardPullback ((Over.pullback b).map f)).hom =
      Functor.whiskerLeft (Over.map b).op (fppfPicardPullback f).hom ≫
        (fppfPicardSheafBaseChangeIso X.hom b).inv := by
  apply (cancel_epi (fppfPicardSheafBaseChangeIso Y.hom b).hom).mp
  apply (cancel_mono (fppfPicardSheafBaseChangeIso X.hom b).hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using fppfPicardPullback_baseChange f b

end BaseChange

end AlgebraicGeometry.Scheme.RelativePicard
