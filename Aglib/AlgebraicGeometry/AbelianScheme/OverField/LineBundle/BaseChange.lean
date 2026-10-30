/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.FamilyFormula
public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.TranslationBaseChange
public import Aglib.AlgebraicGeometry.Picard.BaseChangeRepresentableBy

/-!
# Field base change of the original line-bundle morphism

The field extension uses the original pullback group scheme and the original
base-changed representation of the same Picard scheme. The classifying equation
is compared through the proved whole fppf base-change square and the original
translated-family comparison. No new Picard representative or independent group
law is selected.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {k K : Type u} [Field k] [Field K]
  (s : Spec (.of K) ⟶ Spec (.of k))
  (G : Over (Spec (.of k))) [GrpObj G]
  [IsProper G.hom] [Flat G.hom] [GeometricallyIntegral G.hom]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf G.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

local instance : IsProper ((Over.pullback s).obj G).hom := by
  change IsProper (pullback.snd G.hom s)
  infer_instance

local instance : Flat ((Over.pullback s).obj G).hom := by
  change Flat (pullback.snd G.hom s)
  infer_instance

local instance : GeometricallyIntegral ((Over.pullback s).obj G).hom := by
  change GeometricallyIntegral (pullback.snd G.hom s)
  infer_instance

local instance : LocallyOfFiniteType (LocallyNoetherianOver.baseChange s P).obj.hom := by
  change LocallyOfFiniteType (pullback.snd P.obj.hom s)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Field extension preserves the actual morphism `φ_L`, on the actual
pullback group and the original base-changed Picard representation. -/
theorem lineBundleClassMorphism_baseChange (a : PicardGroup G.left) :
    letI : GrpObj ((Over.pullback s).obj G) := Functor.grpObjObj
    lineBundleClassMorphism ((Over.pullback s).obj G)
        (LocallyNoetherianOver.baseChange s P) (baseChangeRepresentableBy G.hom s P R)
        (pullbackClass (pullback.fst G.hom s) a) =
      (Over.pullback s).map (lineBundleClassMorphism G P R a) := by
  let G' := (Over.pullback s).obj G
  let : GrpObj G' := Functor.grpObjObj
  let P' := LocallyNoetherianOver.baseChange s P
  let R' := baseChangeRepresentableBy G.hom s P R
  let a' := pullbackClass (pullback.fst G.hom s) a
  let T : LocallyNoetherianOver (Spec (.of K)) :=
    ⟨G', LocallyOfFiniteType.isLocallyNoetherian G'.hom⟩
  let T₀ : LocallyNoetherianOver (Spec (.of k)) := ⟨Over.mk (T.obj.hom ≫ s), T.property⟩
  let t₀ : T₀.obj ⟶ G := ((Over.mapPullbackAdj s).homEquiv T.obj G).symm (𝟙 G')
  let E := fppfPicardSheafBaseChangeIso G.hom s
  let q := ((quotientProjection G.hom ≫ toFppfPicardSheaf G.hom).app (op T₀.obj)).hom
  let q' := ((quotientProjection G'.hom ≫ toFppfPicardSheaf G'.hom).app (op T.obj)).hom
  let φ := lineBundleClassMorphism G P R a
  let φ' := lineBundleClassMorphism G' P' R' a'
  have hleft : R'.homEquiv (ObjectProperty.homMk φ' : T ⟶ P') =
      q' (translationFamilyClass G' (𝟙 G') a') := by
    have h := fppf_homEquiv_comp_lineBundleClassMorphism G' P' R' (T := T) (𝟙 G') a'
    exact (congrArg (fun f : G' ⟶ P'.obj =>
      R'.homEquiv (ObjectProperty.homMk f : T ⟶ P')) (Category.id_comp φ')).symm.trans h
  have hfam := translationFamilyClass_baseChange_inv s G (T := T.obj) (𝟙 G') a
  have hleftValue : (E.hom.app (op T.obj)).hom
      (R'.homEquiv (ObjectProperty.homMk φ' : T ⟶ P')) =
        q (translationFamilyClass G t₀ a) := by
    rw [hleft]
    have h := fppfPicardSheafBaseChangeIso_hom_app_toFppfPicardSheaf_mk
      G.hom s (op T.obj) (translationFamilyClass G' (𝟙 G') a')
    change (E.hom.app (op T.obj)).hom (q' (translationFamilyClass G' (𝟙 G') a')) =
      q (pullbackClass (familyBaseChangeIso G.hom s T.obj).inv
        (translationFamilyClass G' (𝟙 G') a')) at h
    exact h.trans (congrArg q hfam)
  have hmap : ((Over.mapPullbackAdj s).homEquiv T.obj P.obj).symm
      ((Over.pullback s).map φ) = t₀ ≫ φ := by
    apply Over.OverMorphism.ext
    change ((Over.pullback s).map φ).left ≫ pullback.fst P.obj.hom s =
      (𝟙 G'.left ≫ pullback.fst G.hom s) ≫ φ.left
    simp
  have hrightValue : (E.hom.app (op T.obj)).hom
      (R'.homEquiv (ObjectProperty.homMk ((Over.pullback s).map φ) : T ⟶ P')) =
        q (translationFamilyClass G t₀ a) := by
    rw [baseChangeRepresentableBy_homEquiv]
    have hc (z : (fppfPicardSheaf G.hom).obj.obj (op T₀.obj)) :
        (E.hom.app (op T.obj)).hom ((E.inv.app (op T.obj)).hom z) = z :=
      congrArg (fun θ => θ.hom z) (E.inv_hom_id_app (op T.obj))
    rw [hc]
    exact (congrArg (fun f : T₀.obj ⟶ P.obj =>
      R.homEquiv (ObjectProperty.homMk f : T₀ ⟶ P)) hmap).trans
        (fppf_homEquiv_comp_lineBundleClassMorphism G P R t₀ a)
  have heq : (ObjectProperty.homMk φ' : T ⟶ P') =
      ObjectProperty.homMk ((Over.pullback s).map φ) := by
    apply R'.homEquiv.injective
    apply (ConcreteCategory.bijective_of_isIso (E.hom.app (op T.obj))).1
    exact hleftValue.trans hrightValue.symm
  exact congrArg (fun f : T ⟶ P' => f.hom) heq

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The line-bundle form uses the original pullback line bundle under field
extension and the same original morphism on the other side. -/
theorem lineBundleMorphism_baseChange (L : LineBundle G.left) :
    letI : GrpObj ((Over.pullback s).obj G) := Functor.grpObjObj
    lineBundleMorphism ((Over.pullback s).obj G)
        (LocallyNoetherianOver.baseChange s P) (baseChangeRepresentableBy G.hom s P R)
        (pullbackLineBundle (pullback.fst G.hom s) L) =
      (Over.pullback s).map (lineBundleMorphism G P R L) := by
  let : GrpObj ((Over.pullback s).obj G) := Functor.grpObjObj
  unfold lineBundleMorphism
  rw [← pullbackClass_classOf]
  exact lineBundleClassMorphism_baseChange s G P R (classOf G.left L)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original first projections give the field-base-change square for
the actual line-bundle morphism, before evaluation at any points. -/
theorem lineBundleClassMorphism_baseChange_fst (a : PicardGroup G.left) :
    letI : GrpObj ((Over.pullback s).obj G) := Functor.grpObjObj
    (lineBundleClassMorphism ((Over.pullback s).obj G)
      (LocallyNoetherianOver.baseChange s P) (baseChangeRepresentableBy G.hom s P R)
      (pullbackClass (pullback.fst G.hom s) a)).left ≫ pullback.fst P.obj.hom s =
      pullback.fst G.hom s ≫ (lineBundleClassMorphism G P R a).left := by
  let : GrpObj ((Over.pullback s).obj G) := Functor.grpObjObj
  rw [lineBundleClassMorphism_baseChange]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual identity-component factor after field extension is compatible
with base change after its original inclusion into the same Picard scheme.
No second realization of the base-changed identity component is introduced. -/
theorem lineBundleClassMorphismIdentityComponent_baseChange_ι (a : PicardGroup G.left) :
    letI : GrpObj ((Over.pullback s).obj G) := Functor.grpObjObj
    letI := picardCommGrpObj ((Over.pullback s).obj G).hom
      (LocallyNoetherianOver.baseChange s P) (baseChangeRepresentableBy G.hom s P R)
    lineBundleClassMorphismIdentityComponent ((Over.pullback s).obj G)
        (LocallyNoetherianOver.baseChange s P) (baseChangeRepresentableBy G.hom s P R)
        (pullbackClass (pullback.fst G.hom s) a) ≫
      Group.identityComponentι (LocallyNoetherianOver.baseChange s P).obj =
      (Over.pullback s).map (lineBundleClassMorphism G P R a) := by
  let : GrpObj ((Over.pullback s).obj G) := Functor.grpObjObj
  let := picardCommGrpObj ((Over.pullback s).obj G).hom
    (LocallyNoetherianOver.baseChange s P) (baseChangeRepresentableBy G.hom s P R)
  exact (lineBundleClassMorphismIdentityComponent_ι ((Over.pullback s).obj G)
    (LocallyNoetherianOver.baseChange s P) (baseChangeRepresentableBy G.hom s P R)
      (pullbackClass (pullback.fst G.hom s) a)).trans
        (lineBundleClassMorphism_baseChange s G P R a)

end AlgebraicGeometry.Scheme.RelativePicard
