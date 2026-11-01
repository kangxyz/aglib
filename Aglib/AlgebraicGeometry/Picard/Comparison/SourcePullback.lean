/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Presheaf.Pullback
public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.Rigidified
public import Aglib.AlgebraicGeometry.Picard.Comparison.Isomorphism
public import Aglib.AlgebraicGeometry.Picard.Comparison.UniversalRigidified
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Source pullback of the original rigidified pairs

The source morphism is arbitrary. For rigidification, its original origin
square is required: `oX ≫ f = oY`. The underlying line bundle is pulled back
along the same `familyMapOfHom f T`; its rigidification uses that actual
origin square and the original module-pullback comparison.

The original pairs, their source identity/composition comparisons and their
parameter-pullback interchange give the whole rigidified Picard morphism.
The original fppf class equation is proved before any supplied representative
is evaluated. There is no flatness hypothesis on `f`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules Scheme.Modules.Invertible

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{u}} {X Y Z W : Over S}
  (oX : 𝟙_ (Over S) ⟶ X) (oY : 𝟙_ (Over S) ⟶ Y)
  (oZ : 𝟙_ (Over S) ⟶ Z) (oW : 𝟙_ (Over S) ⟶ W)

set_option backward.isDefEq.respectTransparency false in
/-- The genuine pointed equation gives the whole original origin square
on every test scheme. -/
@[reassoc]
theorem originSection_comp_familyMapOfHom (f : X ⟶ Y) (hf : oX ≫ f = oY) (T : Over S) :
    originSection X.hom oX.left (Over.w oX) T ≫ familyMapOfHom f T =
      originSection Y.hom oY.left (Over.w oY) T := by
  have h : oX.left ≫ f.left = oY.left := congrArg (fun q => q.left) hf
  apply pullback.hom_ext <;> simp [Category.assoc, h]

namespace RigidifiedPair

set_option backward.isDefEq.respectTransparency false in
/-- Pullback of the actual pair in the source direction, with its
rigidification transported through the actual pointed square. -/
def sourcePullback (f : X ⟶ Y) (hf : oX ≫ f = oY) {T : Over S}
    (Q : RigidifiedPair Y.hom oY.left (Over.w oY) T) :
    RigidifiedPair X.hom oX.left (Over.w oX) T where
  bundle := pullbackLineBundle (familyMapOfHom f T) Q.bundle
  rigidification :=
    (Scheme.Modules.pullbackComp (originSection X.hom oX.left (Over.w oX) T)
      (familyMapOfHom f T)).app Q.bundle.val ≪≫
    (Scheme.Modules.pullbackCongr (originSection_comp_familyMapOfHom oX oY f hf T)).app
      Q.bundle.val ≪≫ Q.rigidification

/-- The source operation uses the original line-bundle pullback. -/
@[simp]
theorem sourcePullback_bundle (f : X ⟶ Y) (hf : oX ≫ f = oY) {T : Over S}
    (Q : RigidifiedPair Y.hom oY.left (Over.w oY) T) :
    (sourcePullback oX oY f hf Q).bundle =
      pullbackLineBundle (familyMapOfHom f T) Q.bundle := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Source pullback of an actual rigidified isomorphism has precisely the
original module pullback as its underlying map. -/
def Iso.sourcePullback (f : X ⟶ Y) (hf : oX ≫ f = oY) {T : Over S}
    {Q Q' : RigidifiedPair Y.hom oY.left (Over.w oY) T} (e : Iso Q Q') :
    Iso (RigidifiedPair.sourcePullback oX oY f hf Q)
      (RigidifiedPair.sourcePullback oX oY f hf Q') where
  iso := (Scheme.Modules.pullback (familyMapOfHom f T)).mapIso e.iso
  comm := by
    have h₁ := (Scheme.Modules.pullbackComp (originSection X.hom oX.left (Over.w oX) T)
      (familyMapOfHom f T)).hom.naturality e.iso.hom
    have h₂ := (Scheme.Modules.pullbackCongr
      (originSection_comp_familyMapOfHom oX oY f hf T)).hom.naturality e.iso.hom
    simp only [RigidifiedPair.sourcePullback, CategoryTheory.Iso.trans_hom,
      CategoryTheory.Functor.mapIso_hom, CategoryTheory.Iso.app_hom]
    rw [reassoc_of% h₁, reassoc_of% h₂, e.comm]

/-- The underlying source-pullback isomorphism is the original module operation. -/
@[simp]
theorem Iso.sourcePullback_iso (f : X ⟶ Y) (hf : oX ≫ f = oY) {T : Over S}
    {Q Q' : RigidifiedPair Y.hom oY.left (Over.w oY) T} (e : Iso Q Q') :
    (Iso.sourcePullback oX oY f hf e).iso =
      (Scheme.Modules.pullback (familyMapOfHom f T)).mapIso e.iso := rfl

/-- Equality of the original pointed morphisms gives the same source pullback. -/
def sourcePullbackCongrIso {f g : X ⟶ Y} (h : f = g)
    (hf : oX ≫ f = oY) (hg : oX ≫ g = oY) {T : Over S}
    (Q : RigidifiedPair Y.hom oY.left (Over.w oY) T) :
    Iso (sourcePullback oX oY f hf Q) (sourcePullback oX oY g hg Q) := by
  subst g
  exact Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/-- Source identity comparison on the same actual pair. -/
def sourcePullbackIdIso {T : Over S}
    (Q : RigidifiedPair X.hom oX.left (Over.w oX) T) :
    Iso (sourcePullback oX oX (𝟙 X) (Category.comp_id oX) Q) Q :=
  isoOfBundleIso _ _
    ((Scheme.Modules.pullbackCongr (familyMapOfHom_id X T)).app Q.bundle.val ≪≫
      (Scheme.Modules.pullbackId _).app Q.bundle.val)

set_option backward.isDefEq.respectTransparency false in
/-- Source composition comparison, using the original module-pullback
composition on the original fibre products. -/
def sourcePullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : oX ≫ f = oY) (hg : oY ≫ g = oZ) {T : Over S}
    (Q : RigidifiedPair Z.hom oZ.left (Over.w oZ) T) :
    Iso (sourcePullback oX oZ (f ≫ g) (by rw [← Category.assoc, hf, hg]) Q)
      (sourcePullback oX oY f hf (sourcePullback oY oZ g hg Q)) :=
  isoOfBundleIso _ _
    ((Scheme.Modules.pullbackCongr (familyMapOfHom_comp f g T)).app Q.bundle.val ≪≫
      ((Scheme.Modules.pullbackComp (familyMapOfHom f T) (familyMapOfHom g T)).app
        Q.bundle.val).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Parameter pullback commutes with source pullback, as an isomorphism of
the actual original pairs and their original rigidifications. -/
def sourcePullbackParameterIso (f : X ⟶ Y) (hf : oX ≫ f = oY)
    {T T' : Over S} (a : T' ⟶ T)
    (Q : RigidifiedPair Y.hom oY.left (Over.w oY) T) :
    Iso (map a (sourcePullback oX oY f hf Q))
      (sourcePullback oX oY f hf (map a Q)) := by
  let aX : pullback X.hom T'.hom ⟶ pullback X.hom T.hom := (familyScheme X.hom).map a
  let aY : pullback Y.hom T'.hom ⟶ pullback Y.hom T.hom := (familyScheme Y.hom).map a
  exact isoOfBundleIso _ _
    ((Scheme.Modules.pullbackComp aX (familyMapOfHom f T)).app Q.bundle.val ≪≫
      (Scheme.Modules.pullbackCongr (familyMapOfHom_naturality f a)).app Q.bundle.val ≪≫
      ((Scheme.Modules.pullbackComp (familyMapOfHom f T') aY).app Q.bundle.val).symm)

set_option backward.isDefEq.respectTransparency false in
/-- Source pullback preserves the original identity isomorphism. -/
theorem Iso.sourcePullback_refl (f : X ⟶ Y) (hf : oX ≫ f = oY) {T : Over S}
    (Q : RigidifiedPair Y.hom oY.left (Over.w oY) T) :
    Iso.sourcePullback oX oY f hf (Iso.refl Q) =
      Iso.refl (RigidifiedPair.sourcePullback oX oY f hf Q) := by
  apply Iso.ext'
  change (Scheme.Modules.pullback (familyMapOfHom f T)).map (𝟙 Q.bundle.val) = _
  exact (Scheme.Modules.pullback (familyMapOfHom f T)).map_id _

set_option backward.isDefEq.respectTransparency false in
/-- Source pullback preserves composition of the original isomorphisms. -/
theorem Iso.sourcePullback_trans (f : X ⟶ Y) (hf : oX ≫ f = oY) {T : Over S}
    {Q Q' Q'' : RigidifiedPair Y.hom oY.left (Over.w oY) T}
    (e : Iso Q Q') (e' : Iso Q' Q'') :
    Iso.sourcePullback oX oY f hf (e.trans e') =
      (Iso.sourcePullback oX oY f hf e).trans (Iso.sourcePullback oX oY f hf e') := by
  apply Iso.ext'
  change (Scheme.Modules.pullback (familyMapOfHom f T)).map (e.iso.hom ≫ e'.iso.hom) = _
  exact (Scheme.Modules.pullback (familyMapOfHom f T)).map_comp _ _

set_option backward.isDefEq.respectTransparency false in
/-- Source pullback preserves the inverse of the original isomorphism. -/
theorem Iso.sourcePullback_symm (f : X ⟶ Y) (hf : oX ≫ f = oY) {T : Over S}
    {Q Q' : RigidifiedPair Y.hom oY.left (Over.w oY) T} (e : Iso Q Q') :
    Iso.sourcePullback oX oY f hf e.symm = (Iso.sourcePullback oX oY f hf e).symm := by
  apply Iso.ext'
  rfl

/-- Source-composition left unit, on the actual comparisons. Universal
O-connectedness is required only at the final source family. -/
theorem sourcePullbackCompIso_id_left (f : X ⟶ Y) (hf : oX ≫ f = oY) {T : Over S}
    [IsIso (pullback.snd X.hom T.hom).c]
    (Q : RigidifiedPair Y.hom oY.left (Over.w oY) T) :
    (sourcePullbackCompIso oX oX oY (𝟙 X) f (Category.comp_id oX) hf Q).trans
        (sourcePullbackIdIso oX (sourcePullback oX oY f hf Q)) =
      sourcePullbackCongrIso oX oY (Category.id_comp f)
        (by simpa only [Category.id_comp] using hf) hf Q :=
  Iso.eq_of_isIso_c X.hom oX.left (Over.w oX) _ _

/-- Source-composition right unit, with the original pulled-back comparison. -/
theorem sourcePullbackCompIso_id_right (f : X ⟶ Y) (hf : oX ≫ f = oY) {T : Over S}
    [IsIso (pullback.snd X.hom T.hom).c]
    (Q : RigidifiedPair Y.hom oY.left (Over.w oY) T) :
    (sourcePullbackCompIso oX oY oY f (𝟙 Y) hf (Category.comp_id oY) Q).trans
        (Iso.sourcePullback oX oY f hf (sourcePullbackIdIso oY Q)) =
      sourcePullbackCongrIso oX oY (Category.comp_id f)
        (by simpa only [Category.comp_id] using hf) hf Q :=
  Iso.eq_of_isIso_c X.hom oX.left (Over.w oX) _ _

/-- Associativity for source pullback uses the original point-preserving
maps and the original composition isomorphisms, before evaluation. -/
theorem sourcePullbackCompIso_assoc
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (hf : oX ≫ f = oY) (hg : oY ≫ g = oZ) (hh : oZ ≫ h = oW)
    {T : Over S} [IsIso (pullback.snd X.hom T.hom).c]
    (Q : RigidifiedPair W.hom oW.left (Over.w oW) T) :
    (sourcePullbackCompIso oX oZ oW (f ≫ g) h
        (by rw [← Category.assoc, hf, hg]) hh Q).trans
      (sourcePullbackCompIso oX oY oZ f g hf hg (sourcePullback oZ oW h hh Q)) =
      (sourcePullbackCongrIso oX oW (Category.assoc f g h)
        (by rw [← Category.assoc, ← Category.assoc, hf, hg, hh])
        (by rw [← Category.assoc, hf, ← Category.assoc, hg, hh]) Q).trans
        ((sourcePullbackCompIso oX oY oW f (g ≫ h) hf
          (by rw [← Category.assoc, hg, hh]) Q).trans
          (Iso.sourcePullback oX oY f hf (sourcePullbackCompIso oY oZ oW g h hg hh Q))) :=
  Iso.eq_of_isIso_c X.hom oX.left (Over.w oX) _ _

/-- The parameter/source interchange respects identity parameter pullback. -/
theorem sourcePullbackParameterIso_id (f : X ⟶ Y) (hf : oX ≫ f = oY) {T : Over S}
    [IsIso (pullback.snd X.hom T.hom).c]
    (Q : RigidifiedPair Y.hom oY.left (Over.w oY) T) :
    (sourcePullbackParameterIso oX oY f hf (𝟙 T) Q).trans
        (Iso.sourcePullback oX oY f hf (mapIdIso Q)) =
      mapIdIso (sourcePullback oX oY f hf Q) :=
  Iso.eq_of_isIso_c X.hom oX.left (Over.w oX) _ _

/-- The parameter/source interchange respects composition on arbitrary
parameter schemes, including nonreduced double and triple bases. -/
theorem sourcePullbackParameterIso_comp (f : X ⟶ Y) (hf : oX ≫ f = oY)
    {T₀ T₁ T₂ : Over S} (a : T₀ ⟶ T₁) (b : T₁ ⟶ T₂)
    [IsIso (pullback.snd X.hom T₀.hom).c]
    (Q : RigidifiedPair Y.hom oY.left (Over.w oY) T₂) :
    (mapCompIso a b (sourcePullback oX oY f hf Q)).trans
        ((Iso.map a (sourcePullbackParameterIso oX oY f hf b Q)).trans
          (sourcePullbackParameterIso oX oY f hf a (map b Q))) =
      (sourcePullbackParameterIso oX oY f hf (a ≫ b) Q).trans
        (Iso.sourcePullback oX oY f hf (mapCompIso a b Q)) :=
  Iso.eq_of_isIso_c X.hom oX.left (Over.w oX) _ _

/-- Source composition and parameter interchange form the same whole
commuting diagram on the original rigidified pairs. -/
theorem sourcePullbackCompIso_parameter
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : oX ≫ f = oY) (hg : oY ≫ g = oZ)
    {T T' : Over S} (a : T' ⟶ T) [IsIso (pullback.snd X.hom T'.hom).c]
    (Q : RigidifiedPair Z.hom oZ.left (Over.w oZ) T) :
    (Iso.map a (sourcePullbackCompIso oX oY oZ f g hf hg Q)).trans
        ((sourcePullbackParameterIso oX oY f hf a (sourcePullback oY oZ g hg Q)).trans
          (Iso.sourcePullback oX oY f hf (sourcePullbackParameterIso oY oZ g hg a Q))) =
      (sourcePullbackParameterIso oX oZ (f ≫ g)
        (by rw [← Category.assoc, hf, hg]) a Q).trans
          (sourcePullbackCompIso oX oY oZ f g hf hg (map a Q)) :=
  Iso.eq_of_isIso_c X.hom oX.left (Over.w oX) _ _

set_option backward.isDefEq.respectTransparency false in
/-- Source pullback of the existing trivial rigidified pair is the existing
trivial pair on the source. Its bundle comparison is obtained from the
module pullback-unit comparison by the existing scalar normalization; no
second trivial-pair model is introduced. -/
def sourcePullbackTrivialIso (f : X ⟶ Y) (hf : oX ≫ f = oY) (T : Over S) :
    Iso (sourcePullback oX oY f hf (trivialRigidifiedPair Y.hom oY.left (Over.w oY) T))
      (trivialRigidifiedPair X.hom oX.left (Over.w oX) T) :=
  isoOfBundleIso _ _
    ((Scheme.Modules.pullback (familyMapOfHom f T)).mapIso
        (coproductUniqueIso (fun _ : PUnit.{u + 1} =>
          SheafOfModules.unit (pullback Y.hom T.hom).ringCatSheaf)) ≪≫
      Scheme.Modules.pullbackUnitIso (familyMapOfHom f T) ≪≫
      (coproductUniqueIso (fun _ : PUnit.{u + 1} =>
        SheafOfModules.unit (pullback X.hom T.hom).ringCatSheaf)).symm)

/-- The source-unit comparison agrees with the original identity comparison. -/
theorem sourcePullbackTrivialIso_id (T : Over S) [IsIso (pullback.snd X.hom T.hom).c] :
    sourcePullbackTrivialIso oX oX (𝟙 X) (Category.comp_id oX) T =
      sourcePullbackIdIso oX (trivialRigidifiedPair X.hom oX.left (Over.w oX) T) :=
  Iso.eq_of_isIso_c X.hom oX.left (Over.w oX) _ _

/-- The original source-unit comparisons are compatible with composition. -/
theorem sourcePullbackTrivialIso_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : oX ≫ f = oY) (hg : oY ≫ g = oZ)
    (T : Over S) [IsIso (pullback.snd X.hom T.hom).c] :
    (sourcePullbackCompIso oX oY oZ f g hf hg
        (trivialRigidifiedPair Z.hom oZ.left (Over.w oZ) T)).trans
      ((Iso.sourcePullback oX oY f hf (sourcePullbackTrivialIso oY oZ g hg T)).trans
        (sourcePullbackTrivialIso oX oY f hf T)) =
      sourcePullbackTrivialIso oX oZ (f ≫ g) (by rw [← Category.assoc, hf, hg]) T :=
  Iso.eq_of_isIso_c X.hom oX.left (Over.w oX) _ _

/-- Source-unit normalization commutes with arbitrary original parameter pullback. -/
theorem sourcePullbackTrivialIso_parameter (f : X ⟶ Y) (hf : oX ≫ f = oY)
    {T T' : Over S} (a : T' ⟶ T) [IsIso (pullback.snd X.hom T'.hom).c] :
    (Iso.map a (sourcePullbackTrivialIso oX oY f hf T)).trans
        (trivialRigidifiedPairMapIso X.hom oX.left (Over.w oX) a) =
      (sourcePullbackParameterIso oX oY f hf a
        (trivialRigidifiedPair Y.hom oY.left (Over.w oY) T)).trans
        ((Iso.sourcePullback oX oY f hf
          (trivialRigidifiedPairMapIso Y.hom oY.left (Over.w oY) a)).trans
          (sourcePullbackTrivialIso oX oY f hf T')) :=
  Iso.eq_of_isIso_c X.hom oX.left (Over.w oX) _ _

end RigidifiedPair

/-- The source operation on the existing rigidified Picard functors. It is
defined on all tests, without any representability or geometry assumption. -/
def rigidifiedPicardPullback (f : X ⟶ Y) (hf : oX ≫ f = oY) :
    rigidifiedPicardFunctor Y.hom oY.left (Over.w oY) ⟶
      rigidifiedPicardFunctor X.hom oX.left (Over.w oX) where
  app T := TypeCat.ofHom (Quotient.map (RigidifiedPair.sourcePullback oX oY f hf)
    (by rintro Q Q' ⟨e⟩; exact ⟨RigidifiedPair.Iso.sourcePullback oX oY f hf e⟩))
  naturality T T' a := by
    ext q
    induction q using Quotient.inductionOn with | h Q =>
    exact Quotient.sound ⟨(RigidifiedPair.sourcePullbackParameterIso oX oY f hf a.unop Q).symm⟩

/-- The source operation retains the original rigidified-pair class. -/
theorem rigidifiedPicardPullback_app_mk (f : X ⟶ Y) (hf : oX ≫ f = oY) {T : Over S}
    (Q : RigidifiedPair Y.hom oY.left (Over.w oY) T) :
    (rigidifiedPicardPullback oX oY f hf).app (op T) (Quotient.mk _ Q) =
      Quotient.mk _ (RigidifiedPair.sourcePullback oX oY f hf Q) := rfl

/-- Whole identity law for the original rigidified Picard operation. -/
@[simp]
theorem rigidifiedPicardPullback_id :
    rigidifiedPicardPullback oX oX (𝟙 X) (Category.comp_id oX) =
      𝟙 (rigidifiedPicardFunctor X.hom oX.left (Over.w oX)) := by
  ext T q
  induction q using Quotient.inductionOn with | h Q =>
  exact Quotient.sound ⟨RigidifiedPair.sourcePullbackIdIso oX Q⟩

/-- Whole contravariant composition for the original rigidified Picard operation. -/
theorem rigidifiedPicardPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : oX ≫ f = oY) (hg : oY ≫ g = oZ) :
    rigidifiedPicardPullback oX oZ (f ≫ g) (by rw [← Category.assoc, hf, hg]) =
      rigidifiedPicardPullback oY oZ g hg ≫ rigidifiedPicardPullback oX oY f hf := by
  ext T q
  induction q using Quotient.inductionOn with | h Q =>
  exact Quotient.sound ⟨RigidifiedPair.sourcePullbackCompIso oX oY oZ f g hf hg Q⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The source-pulled pair has the original fppf pullback class on every
test scheme. Neither representability nor flatness of f is used. -/
theorem sourcePullback_fppfClass (f : X ⟶ Y) (hf : oX ≫ f = oY) {T : Over S}
    (Q : RigidifiedPair Y.hom oY.left (Over.w oY) T) :
    ((quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T)).hom
        (classOf _ (RigidifiedPair.sourcePullback oX oY f hf Q).bundle) =
      ((fppfPicardPullback f).hom.app (op T)).hom
        (((quotientProjection Y.hom ≫ toFppfPicardSheaf Y.hom).app (op T)).hom
          (classOf _ Q.bundle)) := by
  exact (congrArg ((quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T)).hom
    (pullbackClass_classOf (familyMapOfHom f T) Q.bundle)).symm.trans
      (fppfPicardPullback_class f T (classOf _ Q.bundle))

section Comparison

variable [IsLocallyNoetherian S]
  [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom]
  [IsProper Y.hom] [Flat Y.hom] [GeometricallyIntegral Y.hom]

/-- The full original rigidified/fppf comparison square commutes before
evaluation on any universal bundle or locally Noetherian test. -/
theorem rigidifiedPicardPullback_comp_fppfIso (f : X ⟶ Y) (hf : oX ≫ f = oY) :
    rigidifiedPicardPullback oX oY f hf ≫
        (rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral
          X.hom oX.left (Over.w oX)).hom =
      (rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral
        Y.hom oY.left (Over.w oY)).hom ≫
        Functor.whiskerRight (fppfPicardPullback f).hom
          (CategoryTheory.forget AddCommGrpCat.{u + 1}) := by
  ext T q
  induction q using Quotient.inductionOn with | h Q =>
  change (rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral
      X.hom oX.left (Over.w oX)).hom.app T
      (Quotient.mk _ (RigidifiedPair.sourcePullback oX oY f hf Q)) =
    ((fppfPicardPullback f).hom.app T).hom
      ((rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral
        Y.hom oY.left (Over.w oY)).hom.app T (Quotient.mk _ Q))
  rw [rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral_hom,
    rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral_hom]
  change ((toFppfPicardSheaf X.hom).app T).hom
      ((rigidifiedRelativeIso X.hom oX.left (Over.w oX)).hom.app T
        (Quotient.mk _ (RigidifiedPair.sourcePullback oX oY f hf Q))) =
    ((fppfPicardPullback f).hom.app T).hom
      (((toFppfPicardSheaf Y.hom).app T).hom
        ((rigidifiedRelativeIso Y.hom oY.left (Over.w oY)).hom.app T (Quotient.mk _ Q)))
  rw [rigidifiedRelativeIso_hom_app_mk, rigidifiedRelativeIso_hom_app_mk]
  exact sourcePullback_fppfClass oX oY f hf Q

end Comparison

end AlgebraicGeometry.Scheme.RelativePicard
