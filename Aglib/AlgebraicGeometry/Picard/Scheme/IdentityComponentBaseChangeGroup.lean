/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Field
public import Aglib.AlgebraicGeometry.Picard.Scheme.Pullback

/-! The original Picard identity-component base-change comparison as a group isomorphism. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open Scheme.OverField Scheme.Cohomology
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] {X : FScheme k}
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original native component base-change isomorphism, bundled with
its proved structure-map triangle over the extension field. -/
def picardIdentityComponentBaseChangeOverIso (K : Type u) [Field K] [Algebra k K] :
    let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
    fieldBaseChange K (picardIdentityComponent X.hom P R) ≅
      picardIdentityComponent (pullback.snd X.hom b)
        (LocallyNoetherianOver.baseChange b P) (baseChangeRepresentableBy X.hom b P R) := by
  let := picardCommGrpObj X.hom P R
  exact Over.isoMk (picardIdentityComponentBaseChangeIso X.hom P R K)
    (picardIdentityComponentBaseChangeIso_hom_comp X.hom P R K)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same selected component comparison preserves the original whole
inclusion into the base-changed Picard representative. -/
@[reassoc]
theorem picardIdentityComponentBaseChangeOverIso_hom_comp_inclusion
    (K : Type u) [Field K] [Algebra k K] :
    let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
    letI := picardCommGrpObj X.hom P R
    letI := picardCommGrpObj (pullback.snd X.hom b)
      (LocallyNoetherianOver.baseChange b P) (baseChangeRepresentableBy X.hom b P R)
    (picardIdentityComponentBaseChangeOverIso P R K).hom ≫
        picardIdentityComponentι (pullback.snd X.hom b)
          (LocallyNoetherianOver.baseChange b P) (baseChangeRepresentableBy X.hom b P R) =
      (Over.pullback b).map (picardIdentityComponentι X.hom P R) := by
  let := picardCommGrpObj X.hom P R
  apply Over.OverMorphism.ext
  exact picardIdentityComponentBaseChangeIso_hom_ι P R K

private theorem isMonHom_of_mono_comp
    {C : Type*} [Category C] [MonoidalCategory C]
    {A B E : C} [MonObj A] [MonObj B] [MonObj E]
    (f : A ⟶ B) (g : B ⟶ E) [Mono g] [IsMonHom g] [IsMonHom (f ≫ g)] :
    IsMonHom f where
  one_hom := by
    apply (cancel_mono g).mp
    simp only [Category.assoc, IsMonHom.one_hom]
  mul_hom := by
    apply (cancel_mono g).mp
    simp only [Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc]

private theorem isMonHom_map_of_grpObj_eq
    {C E : Type*} [Category C] [Category E]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory E]
    (F : C ⥤ E) [F.Monoidal] {G H : C} [GrpObj G] [GrpObj H]
    (f : G ⟶ H) [IsMonHom f] (M : GrpObj (F.obj H))
    (h : M = Functor.grpObjObj (F := F) (G := H)) :
    letI : GrpObj (F.obj G) := Functor.grpObjObj (F := F) (G := G)
    letI : GrpObj (F.obj H) := M
    IsMonHom (F.map f) := by
  cases h
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original field comparison of the original Picard components
preserves the original monoidal group maps. -/
theorem picardIdentityComponentBaseChangeOverIso_isMonHom
    (K : Type u) [Field K] [Algebra k K] :
    letI := picardCommGrpObj X.hom P R
    let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let J := picardIdentityComponent X.hom P R
    letI : GrpObj (fieldBaseChange K J) :=
      Functor.grpObjObj (F := Over.pullback b) (G := J)
    letI := picardCommGrpObj (pullback.snd X.hom b)
      (LocallyNoetherianOver.baseChange b P) (baseChangeRepresentableBy X.hom b P R)
    IsMonHom (picardIdentityComponentBaseChangeOverIso P R K).hom := by
  let := picardCommGrpObj X.hom P R
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let F := Over.pullback b
  let J := picardIdentityComponent X.hom P R
  let P' := LocallyNoetherianOver.baseChange b P
  let R' := baseChangeRepresentableBy X.hom b P R
  let := picardCommGrpObj (pullback.snd X.hom b) P' R'
  let : GrpObj (fieldBaseChange K J) := by
    change GrpObj ((Over.pullback b).obj J)
    exact Functor.grpObjObj (F := F) (G := J)
  let j := picardIdentityComponentι X.hom P R
  let j' := picardIdentityComponentι (pullback.snd X.hom b) P' R'
  let : IsMonHom j := isMonHom_picardIdentityComponentι X.hom P R
  have hj := isMonHom_map_of_grpObj_eq F j
    (picardCommGrpObj (pullback.snd X.hom b) P' R').toGrpObj
    (picardCommGrpObj_baseChange_toGrpObj X.hom b P R)
  have hcomp : IsMonHom ((picardIdentityComponentBaseChangeOverIso P R K).hom ≫ j') := by
    rw [picardIdentityComponentBaseChangeOverIso_hom_comp_inclusion]
    exact hj
  let := hcomp
  exact isMonHom_of_mono_comp (picardIdentityComponentBaseChangeOverIso P R K).hom j'

/-- The exact same original comparison bundled on the original groups. -/
def picardIdentityComponentBaseChangeGroupIso (K : Type u) [Field K] [Algebra k K] :
    let b := Spec.algebraMap k K
    let P' := LocallyNoetherianOver.baseChange b P
    let R' := baseChangeRepresentableBy X.hom b P R
    letI := picardCommGrpObj X.hom P R
    letI := picardCommGrpObj (pullback.snd X.hom b) P' R'
    (Over.pullback b).mapGrp.obj (Grp.mk (picardIdentityComponent X.hom P R)) ≅
      Grp.mk (picardIdentityComponent (pullback.snd X.hom b) P' R') := by
  let b := Spec.algebraMap k K
  let P' := LocallyNoetherianOver.baseChange b P
  let R' := baseChangeRepresentableBy X.hom b P R
  let := picardCommGrpObj X.hom P R
  let := picardCommGrpObj (pullback.snd X.hom b) P' R'
  let D := picardIdentityComponent X.hom P R
  let D' := picardIdentityComponent (pullback.snd X.hom b) P' R'
  let e : ((Over.pullback b).mapGrp.obj (Grp.mk D)).X ≅ D' :=
    picardIdentityComponentBaseChangeOverIso P R K
  let : IsMonHom e.hom := picardIdentityComponentBaseChangeOverIso_isMonHom P R K
  exact Grp.mkIso' e

end AlgebraicGeometry.Scheme.RelativePicard
