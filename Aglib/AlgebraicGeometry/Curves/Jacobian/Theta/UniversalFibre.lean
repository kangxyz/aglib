/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.UniversalFamily
public import Aglib.AlgebraicGeometry.Curves.Jacobian.DegreeStrata
public import Aglib.AlgebraicGeometry.Picard.Strata.Relation.Basic

/-!
# Actual fibres of the same universal degree family

After the whole test-scheme classification has been proved, a rational
parameter whose translated class is [L] has universal fibre isomorphic to
the original L. The original relative Picard comparison removes only a
line bundle on Spec k, whose class is zero. The canonical family pullback
square and identity-base projection preserve the structural k-action in
the cohomology dimension comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Scheme Scheme.Modules Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Group
open Scheme.Cohomology
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual rational universal fibre has the original curve class,
after the canonical identity-base pullback. -/
theorem degreeUniversalPair_rational_class (n : ℕ) :
    letI := picardCommGrpObj X.hom P R
    ∀ (a : 𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver P.obj) (L : LineBundle X.left),
      a ≫ identityComponentι P.obj ≫ (GrpObj.mulRight (picardPoint P R
        (n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)))).hom =
          picardPoint P R (classOf X.left L) →
      classOf _ (RigidifiedPair.map a (degreeUniversalPair hX o ho P R n)).bundle =
        pullbackClass (pullback.fst X.hom (𝟙 (Spec (.of k)))) (classOf X.left L) := by
  let := picardCommGrpObj X.hom P R
  let := hX.proper
  let := hX.flat
  let := hX.isGeometricallyIntegral
  intro a L ha
  have hf := degreeUniversalPair_classifies hX o ho P R n
    (T := locallyNoetherianRationalPoint k) a
  have hmap : (ObjectProperty.homMk (a ≫ identityComponentι P.obj ≫
      (GrpObj.mulRight (picardPoint P R
        (n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)))).hom) :
        locallyNoetherianRationalPoint k ⟶ P) =
      ObjectProperty.homMk (picardPoint P R (classOf X.left L)) := by
    ext : 1
    exact ha
  have heq := hf.trans ((congrArg R.homEquiv hmap).trans
    (homEquiv_picardPoint P R (classOf X.left L)))
  obtain ⟨b, hb⟩ := (quotientProjection_comp_toFppfPicardSheaf_app_eq_iff X.hom
    (T := 𝟙_ (Over (Spec (.of k)))) _ _).mp heq
  rw [Hom.fieldPicard_eq_zero k b, pullbackClass_zero, add_zero] at hb
  exact hb

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- All cohomology dimensions of the actual universal field fibre agree
with those of L, with the original structural scalar actions. -/
theorem degreeUniversalPair_rational_fibre_dimension (n : ℕ) :
    letI := picardCommGrpObj X.hom P R
    ∀ (a : 𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver P.obj) (L : LineBundle X.left),
      a ≫ identityComponentι P.obj ≫ (GrpObj.mulRight (picardPoint P R
        (n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)))).hom =
          picardPoint P R (classOf X.left L) → ∀ q : ℕ,
      moduleCohomologyDimension
        (pullback.snd (pullback.snd X.hom (identityComponentOver P.obj).hom) a.left)
        ((Scheme.Modules.pullback
          (pullback.fst (pullback.snd X.hom (identityComponentOver P.obj).hom) a.left)).obj
            (degreeUniversalPair hX o ho P R n).bundle.val) q =
        Module.finrank k (moduleCohomology k X L.val q) := by
  let := picardCommGrpObj X.hom P R
  intro a L ha q
  let p := pullback.snd X.hom (identityComponentOver P.obj).hom
  let Q := degreeUniversalPair hX o ho P R n
  let b := (familyScheme X.hom).map a
  let H := Hom.familyMap_isPullback X.hom (identityComponentOver P.obj).hom
    (𝟙 (Spec (.of k))) a.left a.w
  let e := H.isoPullback
  have he : e.hom ≫ pullback.fst p a.left = b := by
    exact H.isoPullback_hom_fst.trans
      (Abel.BoundedFamily.familyScheme_map_eq_familyMap X.hom a).symm
  have hs : e.hom ≫ pullback.snd p a.left = pullback.snd X.hom (𝟙 (Spec (.of k))) :=
    H.isoPullback_hom_snd
  let C : (Scheme.Modules.pullback e.hom).obj
      ((Scheme.Modules.pullback (pullback.fst p a.left)).obj Q.bundle.val) ≅
        (RigidifiedPair.map a Q).bundle.val :=
    (Scheme.Modules.pullbackComp e.hom (pullback.fst p a.left)).app Q.bundle.val ≪≫
      (Scheme.Modules.pullbackCongr he).app Q.bundle.val
  have hc := degreeUniversalPair_rational_class hX o ho P R n a L ha
  have hc' : classOf _ (RigidifiedPair.map a Q).bundle =
      classOf _ (pullbackLineBundle (pullback.fst X.hom (𝟙 (Spec (.of k)))) L) :=
    hc.trans (pullbackClass_classOf _ _)
  obtain ⟨E⟩ := (class_eq_iff _ _ _).mp hc'
  calc
    _ = moduleCohomologyDimension (pullback.snd X.hom (𝟙 (Spec (.of k))))
        (RigidifiedPair.map a Q).bundle.val q :=
      moduleCohomologyDimension_eq_of_isIso e.hom _ _ hs _ C q
    _ = moduleCohomologyDimension (pullback.snd X.hom (𝟙 (Spec (.of k))))
        (pullbackLineBundle (pullback.fst X.hom (𝟙 (Spec (.of k)))) L).val q :=
      moduleCohomologyDimension_congr _ E q
    _ = moduleCohomologyDimension X.hom L.val q :=
      (moduleCohomologyDimension_eq_of_isIso (pullback.fst X.hom (𝟙 (Spec (.of k))))
        X.hom (pullback.snd X.hom (𝟙 (Spec (.of k))))
        (by simpa only [Category.comp_id] using
          pullback.condition (f := X.hom) (g := 𝟙 (Spec (.of k))))
        L.val (Iso.refl _) q).symm
    _ = _ := moduleCohomologyDimension_eq_finrank_moduleCohomology X L.val q

end AlgebraicGeometry.Scheme.OverField.Curve
