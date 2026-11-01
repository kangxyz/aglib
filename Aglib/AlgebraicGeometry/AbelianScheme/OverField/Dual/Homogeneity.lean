/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Poincare
public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.UniversalTranslation
public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.GroupRigidity

/-!
# Homogeneity of the original Poincare family

The universal translation difference is classified on `A × Pic0` through
the original representative. When this native Picard component is proper
and geometrically integral, proper group rigidity makes the classifying
map a homomorphism, and its two zero axes make it zero. These geometric
conditions are explicit: this leaf does not supply the coherent H1 bound
needed by the separate dual-geometry criteria.

The conclusion is an equality of the original family classes. Its arbitrary
test pullbacks include nonreduced schemes; classification is used only on
the original locally Noetherian universal parameter scheme.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules.Invertible Scheme.Group.PointedMorphism

universe u

attribute [local instance] Over.cartesianMonoidalCategory

private theorem geometricallyIntegral_product
    {k : Type u} [Field k] (V W : Over (Spec (.of k)))
    [IsProper V.hom]
    [GeometricallyIntegral V.hom] [GeometricallyIntegral W.hom] :
    GeometricallyIntegral (V ⊗ W).hom := by
  constructor
  intro L _ y Z f g hs
  let F := Over.pullback y
  have hVW : IsIntegral (F.obj V ⊗ F.obj W).left := by dsimp [F]; infer_instance
  have : IsIntegral ((Over.forget (Spec (.of L))).obj (F.obj V ⊗ F.obj W)) := hVW
  let e := (Over.forget (Spec (.of L))).mapIso (Functor.Monoidal.μIso F V W)
  have : IsIntegral (pullback (V ⊗ W).hom y) :=
    IsIntegral.of_isIso e.hom
  exact IsIntegral.of_isIso hs.isoPullback.inv

private theorem rigidity_product
    {k : Type u} [Field k] (V W Y : Over (Spec (.of k)))
    [GrpObj V] [GrpObj W] [GrpObj Y]
    [IsProper V.hom] [IsProper W.hom]
    [GeometricallyIntegral V.hom] [GeometricallyIntegral W.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom]
    (c : V ⊗ W ⟶ Y)
    (hV : lift (𝟙 V) (1 : V ⟶ W) ≫ c = 1)
    (hW : lift (1 : W ⟶ V) (𝟙 W) ≫ c = 1) : c = 1 := by
  have hη : η[V] ≫ lift (𝟙 V) (1 : V ⟶ W) = η[V ⊗ W] := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, Category.comp_id]
      exact (IsMonHom.one_hom (fst V W)).symm
    · rw [Category.assoc, lift_snd]
      calc
        η[V] ≫ (1 : V ⟶ W) = η[W] := by
          simp only [Hom.one_def, ← Category.assoc, comp_toUnit, toUnit_unit,
            Category.id_comp]
        _ = η[V ⊗ W] ≫ snd V W := (IsMonHom.one_hom (snd V W)).symm
  have hunit : η[V ⊗ W] ≫ c = η[Y] := by
    rw [← hη, Category.assoc, hV]
    simp only [Hom.one_def, ← Category.assoc, comp_toUnit, toUnit_unit,
      Category.id_comp]
  have : IsProper (V ⊗ W).hom := by dsimp; infer_instance
  have : GeometricallyIntegral (V ⊗ W).hom := geometricallyIntegral_product V W
  have : IsMonHom c :=
    isMonHom_of_geometricallyIntegral_of_isSeparated (V ⊗ W) Y c hunit
  have hprod : lift (fst V W) (1 : V ⊗ W ⟶ W) *
      lift (1 : V ⊗ W ⟶ V) (snd V W) = 𝟙 (V ⊗ W) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [MonObj.mul_comp, lift_fst, lift_fst, _root_.mul_one, Category.id_comp]
    · rw [MonObj.mul_comp, lift_snd, lift_snd, _root_.one_mul, Category.id_comp]
  have hl : lift (fst V W) (1 : V ⊗ W ⟶ W) ≫ c = 1 := by
    have he : lift (fst V W) (1 : V ⊗ W ⟶ W) =
        fst V W ≫ lift (𝟙 V) (1 : V ⟶ W) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [he, Category.assoc, hV, MonObj.comp_one]
  have hr : lift (1 : V ⊗ W ⟶ V) (snd V W) ≫ c = 1 := by
    have he : lift (1 : V ⊗ W ⟶ V) (snd V W) =
        snd V W ≫ lift (1 : W ⟶ V) (𝟙 W) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [he, Category.assoc, hW, MonObj.comp_one]
  calc
    c = 𝟙 (V ⊗ W) ≫ c := (Category.id_comp c).symm
    _ = (lift (fst V W) (1 : V ⊗ W ⟶ W) *
        lift (1 : V ⊗ W ⟶ V) (snd V W)) ≫ c := by rw [hprod]
    _ = 1 := by rw [MonObj.mul_comp, hl, hr, _root_.mul_one]

private theorem normalizedFamilyClass_eq_zero_of_product_axes
    {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (o : Spec (.of k) ⟶ X) (ho : o ≫ p = 𝟙 _)
    [IsProper p] [GeometricallyIntegral p]
    (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
    [IsSeparated P.obj.hom]
    (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf p).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
    (V W : Over (Spec (.of k))) [GrpObj V] [GrpObj W]
    [IsProper V.hom] [IsProper W.hom]
    [GeometricallyIntegral V.hom] [GeometricallyIntegral W.hom]
    (a : PicardGroup (pullback p (V ⊗ W).hom))
    (hV : pullbackClass ((familyScheme p).map (lift (𝟙 V) (1 : V ⟶ W))) a = 0)
    (hW : pullbackClass ((familyScheme p).map (lift (1 : W ⟶ V) (𝟙 W))) a = 0) :
    normalizedFamilyClass p o ho (V ⊗ W) a = 0 := by
  let := picardCommGrpObj p P R
  have : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian V.hom
  have : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian W.hom
  have : IsProper (V ⊗ W).hom := by dsimp; infer_instance
  have : IsLocallyNoetherian (V ⊗ W).left :=
    LocallyOfFiniteType.isLocallyNoetherian (V ⊗ W).hom
  let T : LocallyNoetherianOver (Spec (.of k)) := ⟨V ⊗ W, inferInstance⟩
  let Rn := normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral p o ho R
  let c : V ⊗ W ⟶ P.obj := (normalizedFamilyClassifyingMap p o ho Rn T a).hom
  have hc {Q : Over (Spec (.of k))} [IsLocallyNoetherian Q.left]
      (f : Q ⟶ V ⊗ W) (hf : pullbackClass ((familyScheme p).map f) a = 0) :
      f ≫ c = 1 := by
    let Qn : LocallyNoetherianOver (Spec (.of k)) := ⟨Q, inferInstance⟩
    let f' : Qn ⟶ T := ObjectProperty.homMk f
    have h := normalizedFamilyClassifyingMap_pullback p o ho Rn f' a
    have h' := congrArg (fun g : Qn ⟶ P => g.hom) h
    change (normalizedFamilyClassifyingMap p o ho Rn Qn
      (pullbackClass ((familyScheme p).map f) a)).hom = f ≫ c at h'
    have hz := congrArg (fun b : PicardGroup (pullback p Q.hom) =>
      (normalizedFamilyClassifyingMap p o ho Rn Qn b).hom) hf
    exact h'.symm.trans (hz.trans (normalizedFamilyClassifyingMap_zero_hom p o ho R Qn))
  have hc1 : c = 1 := rigidity_product V W P.obj c (hc _ hV) (hc _ hW)
  apply (normalizedFamilyClassifyingMap_eq_zero_iff p o ho Rn T a).mp
  apply ObjectProperty.hom_ext
  change c = _
  rw [hc1, normalizedFamilyClassifyingMap_zero_hom p o ho R T]

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [GeometricallyIntegral A.hom]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf A.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The class of the one selected original Poincare bundle, typed on its
literal fibre product. All operations below use this same class. -/
def poincareClass : PicardGroup (pullback A.hom (picardIdentityComponent A.hom P R).hom) :=
  classOf _ (poincareLineBundle A P R)

set_option backward.isDefEq.respectTransparency false in
/-- The original Poincare class vanishes on the source-unit axis. -/
theorem poincareClass_source_unit :
    pullbackClass
        (lift (1 : picardIdentityComponent A.hom P R ⟶ A)
          (𝟙 (picardIdentityComponent A.hom P R))).left
        (poincareClass A P R) = 0 := by
  have h := (poincareRigidifiedPair A P R).classOf_mem_normalizedSubgroup
  change pullbackClass (originSection A.hom η[A].left (by simp)
    (picardIdentityComponent A.hom P R)) (poincareClass A P R) = 0 at h
  rw [originSection_eq_unit_axis] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The original Poincare class vanishes on the parameter-unit axis. -/
theorem poincareClass_parameter_unit :
    pullbackClass (lift (𝟙 A) (1 : A ⟶ picardIdentityComponent A.hom P R)).left
      (poincareClass A P R) = 0 := by
  let q : A.left ⟶ pullback A.hom (picardIdentityComponent A.hom P R).hom :=
    (lift (𝟙 A) (1 : A ⟶ picardIdentityComponent A.hom P R)).left
  change classOf A.left (pullbackLineBundle q (poincareLineBundle A P R)) =
    classOf A.left (trivialLineBundle A.left)
  exact Quotient.sound ⟨poincareParameterUnitIso A P R ≪≫
    (coproductUniqueIso (fun _ : PUnit.{u + 1} =>
      SheafOfModules.unit A.left.ringCatSheaf)).symm⟩

variable [IsSeparated P.obj.hom]
  [IsProper (picardIdentityComponent A.hom P R).hom]
  [GeometricallyIntegral (picardIdentityComponent A.hom P R).hom]

/-- Whole universal homogeneity in the same represented Picard functor.
Properness and geometric integrality concern the actual native component. -/
theorem normalized_poincareUniversalTranslation_eq_zero :
    normalizedFamilyClass A.hom η[A].left (Over.w η[A])
      (A ⊗ picardIdentityComponent A.hom P R)
      (universalTranslationClass A
        (fst A (picardIdentityComponent A.hom P R))
        (snd A (picardIdentityComponent A.hom P R))
        (poincareClass A P R)) = 0 := by
  let D := picardIdentityComponent A.hom P R
  let a := poincareClass A P R
  apply normalizedFamilyClass_eq_zero_of_product_axes A.hom η[A].left (Over.w η[A])
    P R A D
  · rw [universalTranslationClass_pullback, lift_fst, lift_snd]
    exact universalTranslationClass_parameter_one A (𝟙 A) a
      (poincareClass_parameter_unit A P R)
  · rw [universalTranslationClass_pullback, lift_fst, lift_snd]
    exact universalTranslationClass_one A (𝟙 D) a

set_option backward.isDefEq.respectTransparency false in
/-- Original translation homogeneity on every test scheme, including
nonreduced tests. Only the universal classifying argument used Noetherianity. -/
theorem normalized_poincareTranslation_eq_zero
    {T : Over (Spec (.of k))} (t : T ⟶ A)
    (d : T ⟶ picardIdentityComponent A.hom P R) :
    normalizedFamilyClass A.hom η[A].left (Over.w η[A]) T
      (universalTranslationClass A t d (poincareClass A P R)) = 0 := by
  have h := normalizedFamilyClass_pullback A.hom η[A].left (Over.w η[A]) (lift t d)
    (universalTranslationClass A
      (fst A (picardIdentityComponent A.hom P R))
      (snd A (picardIdentityComponent A.hom P R))
      (poincareClass A P R))
  rw [universalTranslationClass_pullback, lift_fst, lift_snd,
    normalized_poincareUniversalTranslation_eq_zero A P R, map_zero] at h
  exact h

/-- The original Poincare coaction equation, with its actual base
pullback correction. No choice of a line-bundle representative occurs. -/
theorem poincareTranslationClass_eq_basePullback
    {T : Over (Spec (.of k))} (t : T ⟶ A)
    (d : T ⟶ picardIdentityComponent A.hom P R) :
    universalTranslationClass A t d (poincareClass A P R) =
      pullbackClass (pullback.snd A.hom T.hom)
        (pullbackClass (lift t d).left (poincareClass A P R)) := by
  have h := congrArg Subtype.val (normalized_poincareTranslation_eq_zero A P R t d)
  rw [normalized_universalTranslationClass_val A t d _ (poincareClass_source_unit A P R)] at h
  exact sub_eq_zero.mp h

set_option backward.isDefEq.respectTransparency false in
/-- The actual normalized translated bundle is trivial as a rigidified
pair, on every test scheme. This uses the existing normalization constructor. -/
def poincareNormalizedTranslationIso
    {T : Over (Spec (.of k))} (t : T ⟶ A)
    (d : T ⟶ picardIdentityComponent A.hom P R) :
    RigidifiedPair.Iso
      (normalizedFamilyRigidifiedPair A.hom η[A].left (Over.w η[A]) T
        (universalTranslationLineBundle A t d (poincareLineBundle A P R)))
      (trivialRigidifiedPair A.hom η[A].left (Over.w η[A]) T) := by
  apply RigidifiedPair.isoOfBundleIso
  apply Classical.choice
  apply (class_eq_iff _ _ _).mp
  change classOf _ (normalizedFamilyLineBundle A.hom η[A].left (Over.w η[A]) T
      (universalTranslationLineBundle A t d (poincareLineBundle A P R))) =
    classOf _ (trivialLineBundle _)
  rw [classOf_normalizedFamilyLineBundle, classOf_universalTranslationLineBundle]
  change (normalizedFamilyClass A.hom η[A].left (Over.w η[A]) T
    (universalTranslationClass A t d (poincareClass A P R))).val =
      classOf _ (trivialLineBundle _)
  rw [normalized_poincareTranslation_eq_zero, classOf_trivial]
  rfl

omit [IsSeparated P.obj.hom] [IsProper (picardIdentityComponent A.hom P R).hom]
  [GeometricallyIntegral (picardIdentityComponent A.hom P R).hom] in
/-- Source-unit normalization makes the actual translated trivialization
unique, including on nonreduced test schemes. -/
theorem poincareNormalizedTranslationIso_unique
    {T : Over (Spec (.of k))} (t : T ⟶ A)
    (d : T ⟶ picardIdentityComponent A.hom P R)
    (e e' : RigidifiedPair.Iso
      (normalizedFamilyRigidifiedPair A.hom η[A].left (Over.w η[A]) T
        (universalTranslationLineBundle A t d (poincareLineBundle A P R)))
      (trivialRigidifiedPair A.hom η[A].left (Over.w η[A]) T)) :
    e = e' :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    A.hom η[A].left (Over.w η[A]) _ _

end AlgebraicGeometry.Scheme.RelativePicard
