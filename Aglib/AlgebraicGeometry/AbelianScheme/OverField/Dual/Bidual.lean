/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Homogeneity
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.FamilyFormula
public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.SourcePullback
public import Aglib.AlgebraicGeometry.Picard.Scheme.Pullback

/-!
# The canonical bidual map from the original Poincare bundle

Transpose the already selected Poincare bundle on `A × Pic0(A)` and classify
its original fppf class through the supplied representative of `Pic(Pic0(A))`.
The original source rigidification supplies the parameter-unit equation.
Connectedness then factors the actual morphism through the native identity
component. Properness and geometric integrality of `Pic0(A)` are not inputs.

Representation is used on locally Noetherian tests only. The actual bundle
and the universal fppf-section pullback equations cover arbitrary tests,
including nonreduced ones. No bidual isomorphism is asserted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local
open Scheme.Group

universe u

attribute [local instance] Over.cartesianMonoidalCategory

private theorem familyFppfClass_naturality {S X : Scheme.{u}} (p : X ⟶ S)
    {T T' : Over S} (f : T' ⟶ T) (a : PicardGroup (pullback p T.hom)) :
    ((quotientProjection p ≫ toFppfPicardSheaf p).app (op T')).hom
        (pullbackClass ((familyScheme p).map f) a) =
      ((fppfPicardSheaf p).obj.map f.op).hom
        (((quotientProjection p ≫ toFppfPicardSheaf p).app (op T)).hom a) := by
  exact congrArg (fun q => q.hom a)
    ((quotientProjection p ≫ toFppfPicardSheaf p).naturality f.op)

private theorem familyMapOfHom_comp_swap {S : Scheme.{u}} {X Y T : Over S}
    (f : X ⟶ Y) :
    familyMapOfHom f T ≫ (β_ Y T).hom.left =
      (β_ X T).hom.left ≫ (familyScheme T.hom).map f := by
  apply pullback.hom_ext <;> simp [Category.assoc]

private theorem swap_comp_familyMapOfHom {S : Scheme.{u}} {X Y T : Over S}
    (f : X ⟶ Y) :
    (β_ T X).hom.left ≫ familyMapOfHom f T =
      (familyScheme T.hom).map f ≫ (β_ T Y).hom.left := by
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- Source-unit normalization preserves the original fppf Picard class. -/
theorem fppfClass_normalizedFamilyClass_val
    {S X : Scheme.{u}} [IsLocallyNoetherian S] (p : X ⟶ S)
    (o : S ⟶ X) (ho : o ≫ p = 𝟙 S) [IsProper p] [Flat p] [GeometricallyIntegral p]
    (T : Over S) (a : PicardGroup (pullback p T.hom)) :
    ((quotientProjection p ≫ toFppfPicardSheaf p).app (op T)).hom
        (normalizedFamilyClass p o ho T a).val =
      ((quotientProjection p ≫ toFppfPicardSheaf p).app (op T)).hom a := by
  rw [← normalizedFamilyClass_fppf p o ho T (normalizedFamilyClass p o ho T a).val,
    normalizedFamilyClass_normalized, normalizedFamilyClass_fppf]

section Construction

variable {k : Type u} [Field k] (A : Over (Spec (.of k)))
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf A.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The native braiding, typed between the original literal fibre products. -/
def poincareTranspose :
    pullback (picardIdentityComponent A.hom P R).hom A.hom ⟶
      pullback A.hom (picardIdentityComponent A.hom P R).hom :=
  (β_ (picardIdentityComponent A.hom P R) A).hom.left

/-- The source-unit square of the transposed family is the original
parameter-unit square, as an equality of whole scheme maps. -/
theorem originSection_comp_poincareTranspose :
    originSection (picardIdentityComponent A.hom P R).hom
        η[picardIdentityComponent A.hom P R].left
        (Over.w η[picardIdentityComponent A.hom P R]) A ≫ poincareTranspose A P R =
      (lift (𝟙 A) (1 : A ⟶ picardIdentityComponent A.hom P R)).left := by
  let D := picardIdentityComponent A.hom P R
  rw [originSection_eq_unit_axis]
  change (lift (1 : A ⟶ D) (𝟙 A) ≫ (β_ D A).hom).left = _
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, braiding_hom_fst, lift_snd]
    exact (CartesianMonoidalCategory.lift_fst (𝟙 A) (1 : A ⟶ D)).symm
  · rw [Category.assoc, braiding_hom_snd, lift_fst]
    exact (CartesianMonoidalCategory.lift_snd (𝟙 A) (1 : A ⟶ D)).symm

variable [GrpObj A] [IsProper A.hom] [GeometricallyIntegral A.hom]

/-- The transposed family is a literal pullback of the one original bundle. -/
def bidualFamilyLineBundle :
    LineBundle (pullback (picardIdentityComponent A.hom P R).hom A.hom) :=
  pullbackLineBundle (poincareTranspose A P R) (poincareLineBundle A P R)

/-- The class of that same transposed original family. -/
def bidualFamilyClass :
    PicardGroup (pullback (picardIdentityComponent A.hom P R).hom A.hom) :=
  pullbackClass (poincareTranspose A P R) (poincareClass A P R)

/-- The bundle and class constructions retain exactly the same original pullback. -/
theorem classOf_bidualFamilyLineBundle :
    classOf _ (bidualFamilyLineBundle A P R) = bidualFamilyClass A P R := rfl

/-- The original parameter-unit trivialization rigidifies the transposed
actual bundle along the source unit of the same native Picard component. -/
def bidualOriginIso :
    (Scheme.Modules.pullback
      (originSection (picardIdentityComponent A.hom P R).hom
        η[picardIdentityComponent A.hom P R].left
        (Over.w η[picardIdentityComponent A.hom P R]) A)).obj
        (bidualFamilyLineBundle A P R).val ≅
      (SheafOfModules.unit A.left.ringCatSheaf : A.left.Modules) :=
  (Scheme.Modules.pullbackComp _ (poincareTranspose A P R)).app
      (poincareLineBundle A P R).val ≪≫
    (Scheme.Modules.pullbackCongr (originSection_comp_poincareTranspose A P R)).app
      (poincareLineBundle A P R).val ≪≫ poincareParameterUnitIso A P R

/-- The transposed original Poincare family, with its actual source rigidification. -/
def bidualRigidifiedPair :
    RigidifiedPair (picardIdentityComponent A.hom P R).hom
      η[picardIdentityComponent A.hom P R].left
      (Over.w η[picardIdentityComponent A.hom P R]) A where
  bundle := bidualFamilyLineBundle A P R
  rigidification := bidualOriginIso A P R

/-- The original source rigidification makes the transposed parameter-unit
restriction trivial. No geometry of the Picard component is used. -/
theorem bidualFamilyClass_parameter_unit :
    pullbackClass ((familyScheme (picardIdentityComponent A.hom P R).hom).map η[A])
      (bidualFamilyClass A P R) = 0 := by
  let D := picardIdentityComponent A.hom P R
  have h : translationFamilyMap D η[A] ≫ (β_ D A).hom =
      (ρ_ D).hom ≫ lift (1 : D ⟶ A) (𝟙 D) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, braiding_hom_fst, translationFamilyMap, lift_snd,
        lift_fst, MonObj.comp_one]
      rw [Hom.one_def]
      congr 1
      exact toUnit_unique _ _
    · simp [translationFamilyMap, rightUnitor_hom]
  have hs : (familyScheme D.hom).map η[A] ≫ poincareTranspose A P R =
      (ρ_ D).hom.left ≫ (lift (1 : D ⟶ A) (𝟙 D)).left := by
    rw [← translationFamilyMap_left]
    exact congrArg (fun q : D ⊗ 𝟙_ (Over (Spec (.of k))) ⟶ A ⊗ D => q.left) h
  rw [bidualFamilyClass, ← pullbackClass_comp, hs, pullbackClass_comp,
    poincareClass_source_unit, pullbackClass_zero]

/-- Parameter-unit triviality pulls back to every original test scheme. -/
theorem bidualFamilyClass_pullback_one (T : Over (Spec (.of k))) :
    pullbackClass ((familyScheme (picardIdentityComponent A.hom P R).hom).map
      (1 : T ⟶ A)) (bidualFamilyClass A P R) = 0 := by
  rw [Hom.one_def, Functor.map_comp, pullbackClass_comp,
    bidualFamilyClass_parameter_unit, pullbackClass_zero]

variable (Q : LocallyNoetherianOver (Spec (.of k)))
  (S : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf (picardIdentityComponent A.hom P R).hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)

/-- Classify the transposed original bundle through the supplied fppf
representative of Pic(DA). This uses only its LN test A. -/
def bidualPicardMorphism : A ⟶ Q.obj :=
  (S.homEquiv.symm
    (((quotientProjection (picardIdentityComponent A.hom P R).hom ≫
      toFppfPicardSheaf (picardIdentityComponent A.hom P R).hom).app (op A)).hom
        (bidualFamilyClass A P R)) :
    (⟨A, LocallyOfFiniteType.isLocallyNoetherian A.hom⟩ :
      LocallyNoetherianOver (Spec (.of k))) ⟶ Q).hom

/-- The actual fppf classifying equation for the one transposed family. -/
theorem homEquiv_bidualPicardMorphism :
    S.homEquiv
      (ObjectProperty.homMk (bidualPicardMorphism A P R Q S) :
        (⟨A, LocallyOfFiniteType.isLocallyNoetherian A.hom⟩ :
          LocallyNoetherianOver (Spec (.of k))) ⟶ Q) =
      ((quotientProjection (picardIdentityComponent A.hom P R).hom ≫
        toFppfPicardSheaf (picardIdentityComponent A.hom P R).hom).app (op A)).hom
          (bidualFamilyClass A P R) :=
  S.homEquiv.apply_symm_apply _

/-- Classification of every original LN parameter pullback. The represented
test category is not enlarged. -/
theorem homEquiv_comp_bidualPicardMorphism
    {T : LocallyNoetherianOver (Spec (.of k))} (t : T.obj ⟶ A) :
    S.homEquiv (ObjectProperty.homMk (t ≫ bidualPicardMorphism A P R Q S) : T ⟶ Q) =
      ((quotientProjection (picardIdentityComponent A.hom P R).hom ≫
        toFppfPicardSheaf (picardIdentityComponent A.hom P R).hom).app (op T.obj)).hom
          (pullbackClass ((familyScheme (picardIdentityComponent A.hom P R).hom).map t)
            (bidualFamilyClass A P R)) := by
  let TA : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨A, LocallyOfFiniteType.isLocallyNoetherian A.hom⟩
  have h := S.homEquiv_comp (ObjectProperty.homMk t : T ⟶ TA)
    (ObjectProperty.homMk (bidualPicardMorphism A P R Q S) : TA ⟶ Q)
  change S.homEquiv (ObjectProperty.homMk (t ≫ bidualPicardMorphism A P R Q S)) =
    ((fppfPicardSheaf (picardIdentityComponent A.hom P R).hom).obj.map t.op).hom
      (S.homEquiv (ObjectProperty.homMk (bidualPicardMorphism A P R Q S) : TA ⟶ Q)) at h
  rw [homEquiv_bidualPicardMorphism] at h
  exact h.trans (familyFppfClass_naturality _ t _).symm

/-- The original universal fppf section has the transposed-family pullback
class on every test, without extending the supplied representability. -/
theorem universalFppfClass_bidualPicardMorphism
    {T : Over (Spec (.of k))} (t : T ⟶ A) :
    ((fppfPicardSheaf (picardIdentityComponent A.hom P R).hom).obj.map
        (t ≫ bidualPicardMorphism A P R Q S).op).hom (S.homEquiv (𝟙 Q)) =
      ((quotientProjection (picardIdentityComponent A.hom P R).hom ≫
        toFppfPicardSheaf (picardIdentityComponent A.hom P R).hom).app (op T)).hom
          (pullbackClass ((familyScheme (picardIdentityComponent A.hom P R).hom).map t)
            (bidualFamilyClass A P R)) := by
  let TA : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨A, LocallyOfFiniteType.isLocallyNoetherian A.hom⟩
  have hu :
      ((fppfPicardSheaf (picardIdentityComponent A.hom P R).hom).obj.map
        (bidualPicardMorphism A P R Q S).op).hom (S.homEquiv (𝟙 Q)) =
      ((quotientProjection (picardIdentityComponent A.hom P R).hom ≫
        toFppfPicardSheaf (picardIdentityComponent A.hom P R).hom).app (op A)).hom
          (bidualFamilyClass A P R) :=
    (S.homEquiv_eq (ObjectProperty.homMk
      (bidualPicardMorphism A P R Q S) : TA ⟶ Q)).symm.trans
        (homEquiv_bidualPicardMorphism A P R Q S)
  rw [op_comp, Functor.map_comp]
  change ((fppfPicardSheaf (picardIdentityComponent A.hom P R).hom).obj.map t.op).hom
    (((fppfPicardSheaf (picardIdentityComponent A.hom P R).hom).obj.map
      (bidualPicardMorphism A P R Q S).op).hom (S.homEquiv (𝟙 Q))) = _
  rw [hu]
  exact (familyFppfClass_naturality _ t _).symm

variable [LocallyOfFiniteType Q.obj.hom]

/-- The actual classifying morphism preserves the original unit. -/
theorem bidualPicardMorphism_pointed :
    letI := picardCommGrpObj (picardIdentityComponent A.hom P R).hom Q S
    η[A] ≫ bidualPicardMorphism A P R Q S = η[Q.obj] := by
  let := picardCommGrpObj (picardIdentityComponent A.hom P R).hom Q S
  let T : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨𝟙_ _, inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))⟩
  have h : (ObjectProperty.homMk (η[A] ≫ bidualPicardMorphism A P R Q S) : T ⟶ Q) =
      ObjectProperty.homMk η[Q.obj] := by
    apply S.homEquiv.injective
    rw [homEquiv_comp_bidualPicardMorphism, bidualFamilyClass_parameter_unit, map_zero]
    symm
    simpa only [MonObj.one_eq_one] using
      picard_homEquiv_one (picardIdentityComponent A.hom P R).hom Q S T
  exact congrArg (fun q : T ⟶ Q => q.hom) h

/-- Connectedness of the original A factors the actual map through the
original identity component of the supplied second representative. -/
theorem range_bidualPicardMorphism_subset_identityComponent :
    letI := picardCommGrpObj (picardIdentityComponent A.hom P R).hom Q S
    Set.range (bidualPicardMorphism A P R Q S).left ⊆ identityComponent Q.obj := by
  let := picardCommGrpObj (picardIdentityComponent A.hom P R).hom Q S
  let : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  exact range_subset_identityComponent_of_section Q.obj _ η[A]
    (bidualPicardMorphism_pointed A P R Q S)

/-- The canonical native bidual map defined by the swapped original
Poincare bundle. No second Poincare bundle is constructed. -/
def bidualMorphism :
    A ⟶ picardIdentityComponent (picardIdentityComponent A.hom P R).hom Q S :=
  letI := picardCommGrpObj (picardIdentityComponent A.hom P R).hom Q S
  liftIdentityComponent Q.obj (bidualPicardMorphism A P R Q S)
    (range_bidualPicardMorphism_subset_identityComponent A P R Q S)

/-- Inclusion into the same supplied second Picard representative recovers
the original classifying morphism. -/
@[reassoc (attr := simp)]
theorem bidualMorphism_ι :
    bidualMorphism A P R Q S ≫
      picardIdentityComponentι (picardIdentityComponent A.hom P R).hom Q S =
        bidualPicardMorphism A P R Q S := by
  let := picardCommGrpObj (picardIdentityComponent A.hom P R).hom Q S
  exact liftIdentityComponent_ι ..

/-- The canonical bidual map preserves the original group unit. -/
theorem bidualMorphism_pointed :
    η[A] ≫ bidualMorphism A P R Q S =
      η[picardIdentityComponent (picardIdentityComponent A.hom P R).hom Q S] := by
  let := picardCommGrpObj (picardIdentityComponent A.hom P R).hom Q S
  let : IsMonHom (picardIdentityComponentι (picardIdentityComponent A.hom P R).hom Q S) :=
    isMonHom_picardIdentityComponentι _ Q S
  rw [← cancel_mono (picardIdentityComponentι (picardIdentityComponent A.hom P R).hom Q S),
    Category.assoc, bidualMorphism_ι, bidualPicardMorphism_pointed, IsMonHom.one_hom]

/-- The original represented class of the actual bidual map, on LN tests. -/
theorem homEquiv_comp_bidualMorphism
    {T : LocallyNoetherianOver (Spec (.of k))} (t : T.obj ⟶ A) :
    S.homEquiv (ObjectProperty.homMk
      ((t ≫ bidualMorphism A P R Q S) ≫
        picardIdentityComponentι (picardIdentityComponent A.hom P R).hom Q S) : T ⟶ Q) =
      ((quotientProjection (picardIdentityComponent A.hom P R).hom ≫
        toFppfPicardSheaf (picardIdentityComponent A.hom P R).hom).app (op T.obj)).hom
          (pullbackClass ((familyScheme (picardIdentityComponent A.hom P R).hom).map t)
            (bidualFamilyClass A P R)) := by
  rw [Category.assoc, bidualMorphism_ι]
  exact homEquiv_comp_bidualPicardMorphism A P R Q S t

/-- The original classifying equation at A itself retains the same
transposed bundle class and the original component inclusion. -/
theorem homEquiv_bidualMorphism :
    S.homEquiv (ObjectProperty.homMk
      (bidualMorphism A P R Q S ≫
        picardIdentityComponentι (picardIdentityComponent A.hom P R).hom Q S) :
      (⟨A, LocallyOfFiniteType.isLocallyNoetherian A.hom⟩ :
        LocallyNoetherianOver (Spec (.of k))) ⟶ Q) =
      ((quotientProjection (picardIdentityComponent A.hom P R).hom ≫
        toFppfPicardSheaf (picardIdentityComponent A.hom P R).hom).app (op A)).hom
          (bidualFamilyClass A P R) := by
  rw [bidualMorphism_ι]
  exact homEquiv_bidualPicardMorphism A P R Q S

/-- Whole universal-class classification of the native bidual map on
arbitrary, possibly nonreduced or non-Noetherian tests. -/
theorem universalFppfClass_bidualMorphism {T : Over (Spec (.of k))} (t : T ⟶ A) :
    ((fppfPicardSheaf (picardIdentityComponent A.hom P R).hom).obj.map
        ((t ≫ bidualMorphism A P R Q S) ≫
          picardIdentityComponentι (picardIdentityComponent A.hom P R).hom Q S).op).hom
      (S.homEquiv (𝟙 Q)) =
      ((quotientProjection (picardIdentityComponent A.hom P R).hom ≫
        toFppfPicardSheaf (picardIdentityComponent A.hom P R).hom).app (op T)).hom
          (pullbackClass ((familyScheme (picardIdentityComponent A.hom P R).hom).map t)
            (bidualFamilyClass A P R)) := by
  rw [Category.assoc, bidualMorphism_ι]
  exact universalFppfClass_bidualPicardMorphism A P R Q S t

/-- The same original bidual map is a group homomorphism. Only the target
representative's separatedness is added; source A supplies proper rigidity. -/
theorem isMonHom_bidualMorphism [IsSeparated Q.obj.hom] :
    IsMonHom (bidualMorphism A P R Q S) := by
  let := picardCommGrpObj (picardIdentityComponent A.hom P R).hom Q S
  have : IsSeparated (identityComponentOver Q.obj).hom := by
    change IsSeparated ((identityComponent Q.obj).ι ≫ Q.obj.hom)
    infer_instance
  exact Group.PointedMorphism.isMonHom_of_geometricallyIntegral_of_isSeparated
    A (identityComponentOver Q.obj) _ (bidualMorphism_pointed A P R Q S)

/-- Bundle the same canonical map in the existing category of group schemes. -/
def bidualGroupHom [IsSeparated Q.obj.hom] :
    Grp.mk A ⟶ Grp.mk (picardIdentityComponent (picardIdentityComponent A.hom P R).hom Q S) :=
  letI := isMonHom_bidualMorphism A P R Q S
  Grp.ofHom (bidualMorphism A P R Q S)

/-- Bundling retains the exact underlying native bidual morphism. -/
@[simp]
theorem bidualGroupHom_hom_hom [IsSeparated Q.obj.hom] :
    (bidualGroupHom A P R Q S).hom.hom = bidualMorphism A P R Q S := rfl

end Construction

section PoincareFunctoriality

variable {k : Type u} [Field k] (A B : Over (Spec (.of k))) [GrpObj A] [GrpObj B]
  [IsProper A.hom] [GeometricallyIntegral A.hom]
  [IsProper B.hom] [GeometricallyIntegral B.hom]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf A.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  (P' : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P'.obj.hom]
  (R' : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf B.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P')

/-- Restriction of the already constructed universal comparison to the
original identity components. Both bundles are the originally selected ones;
neither Picard component is assumed proper or geometrically integral. -/
def poincareIdentityComponentPullbackIso (f : A ⟶ B) (hf : η[A] ≫ f = η[B]) :
    RigidifiedPair.Iso
      (poincarePullback A P R (picardIdentityComponentPullback P R P' R' f))
      (RigidifiedPair.sourcePullback η[A] η[B] f hf (poincareRigidifiedPair B P' R')) := by
  letI := picardCommGrpObj A.hom P R
  letI := picardCommGrpObj B.hom P' R'
  have h : picardIdentityComponentPullback P R P' R' f ≫
      picardIdentityComponentι A.hom P R =
      picardIdentityComponentι B.hom P' R' ≫ picardPullback P R P' R' f :=
    picardIdentityComponentPullback_ι P R P' R' f
  exact (poincareUniversalPullbackIso A P R
    (picardIdentityComponentPullback P R P' R' f)).symm.trans
      ((RigidifiedPair.mapCongrIso h (picardUniversalRigidifiedPair A P R)).trans
        (picardPullbackUniversalPullbackIso P R P' R' η[A] η[B] f hf
          (picardIdentityComponentι B.hom P' R')))

/-- The same original comparison on every parameter scheme is obtained by
actual parameter pullback and the existing source/parameter interchange. -/
def poincareIdentityComponentPullbackParameterIso (f : A ⟶ B)
    (hf : η[A] ≫ f = η[B]) {T : Over (Spec (.of k))}
    (t : T ⟶ picardIdentityComponent B.hom P' R') :
    RigidifiedPair.Iso
      (poincarePullback A P R (t ≫ picardIdentityComponentPullback P R P' R' f))
      (RigidifiedPair.sourcePullback η[A] η[B] f hf (poincarePullback B P' R' t)) :=
  (poincarePullbackCompIso A P R t (picardIdentityComponentPullback P R P' R' f)).trans
    ((RigidifiedPair.Iso.map t (poincareIdentityComponentPullbackIso A B P R P' R' f hf)).trans
      (RigidifiedPair.sourcePullbackParameterIso η[A] η[B] f hf t
        (poincareRigidifiedPair B P' R')))

/-- The whole original comparison is unique on arbitrary parameter tests;
the required geometry belongs only to the original source A. -/
theorem poincareIdentityComponentPullbackParameterIso_unique (f : A ⟶ B)
    (hf : η[A] ≫ f = η[B]) {T : Over (Spec (.of k))}
    (t : T ⟶ picardIdentityComponent B.hom P' R')
    (e e' : RigidifiedPair.Iso
      (poincarePullback A P R (t ≫ picardIdentityComponentPullback P R P' R' f))
      (RigidifiedPair.sourcePullback η[A] η[B] f hf (poincarePullback B P' R' t))) : e = e' :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    A.hom η[A].left (Over.w η[A]) _ _

/-- The universal original Poincare class equation for a pointed source map. -/
theorem poincareClass_picardIdentityComponentPullback (f : A ⟶ B)
    (hf : η[A] ≫ f = η[B]) :
    pullbackClass ((familyScheme A.hom).map (picardIdentityComponentPullback P R P' R' f))
        (poincareClass A P R) =
      pullbackClass (familyMapOfHom f (picardIdentityComponent B.hom P' R'))
        (poincareClass B P' R') := by
  let DA := picardIdentityComponent A.hom P R
  let DB := picardIdentityComponent B.hom P' R'
  let fdual : DB ⟶ DA := picardIdentityComponentPullback P R P' R' f
  let qa : pullback A.hom DB.hom ⟶ pullback A.hom DA.hom := (familyScheme A.hom).map fdual
  let qb : pullback A.hom DB.hom ⟶ pullback B.hom DB.hom := familyMapOfHom f DB
  change classOf (pullback A.hom DB.hom) (pullbackLineBundle qa (poincareLineBundle A P R)) =
    classOf (pullback A.hom DB.hom) (pullbackLineBundle qb (poincareLineBundle B P' R'))
  exact Quotient.sound ⟨(poincareIdentityComponentPullbackIso A B P R P' R' f hf).iso⟩

/-- Swapping the actual Poincare comparison gives the original source-
pullback/parameter-pullback equality needed by bidual naturality. -/
theorem bidualFamilyClass_sourcePullback (f : A ⟶ B) (hf : η[A] ≫ f = η[B]) :
    pullbackClass (familyMapOfHom (picardIdentityComponentPullback P R P' R' f) A)
        (bidualFamilyClass A P R) =
      pullbackClass ((familyScheme (picardIdentityComponent B.hom P' R').hom).map f)
        (bidualFamilyClass B P' R') := by
  let DA := picardIdentityComponent A.hom P R
  let DB := picardIdentityComponent B.hom P' R'
  let fdual : DB ⟶ DA := picardIdentityComponentPullback P R P' R' f
  have h := congrArg (pullbackClass (β_ DB A).hom.left)
    (poincareClass_picardIdentityComponentPullback A B P R P' R' f hf)
  simp only [← pullbackClass_comp] at h
  change pullbackClass (familyMapOfHom fdual A)
      (pullbackClass (β_ DA A).hom.left (poincareClass A P R)) =
    pullbackClass ((familyScheme DB.hom).map f)
      (pullbackClass (β_ DB B).hom.left (poincareClass B P' R'))
  rw [← pullbackClass_comp, ← pullbackClass_comp,
    familyMapOfHom_comp_swap, ← swap_comp_familyMapOfHom]
  exact h

end PoincareFunctoriality

section Naturality

variable {k : Type u} [Field k] (A B : Over (Spec (.of k))) [GrpObj A] [GrpObj B]
  [IsProper A.hom] [GeometricallyIntegral A.hom]
  [IsProper B.hom] [GeometricallyIntegral B.hom]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf A.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  (P' : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P'.obj.hom]
  (R' : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf B.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P')
  (Q : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType Q.obj.hom]
  (S : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf (picardIdentityComponent A.hom P R).hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)
  (Q' : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType Q'.obj.hom]
  (S' : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf (picardIdentityComponent B.hom P' R').hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q')

/-- Naturality of the canonical bidual map for the original pointed source
map and the original Picard pullback applied twice. All four representing
schemes are the supplied ones; no geometry of DA or DB is assumed. -/
theorem bidualMorphism_naturality (f : A ⟶ B) (hf : η[A] ≫ f = η[B]) :
    bidualMorphism A P R Q S ≫
      picardIdentityComponentPullback Q' S' Q S
        (picardIdentityComponentPullback P R P' R' f) =
      f ≫ bidualMorphism B P' R' Q' S' := by
  let DA := picardIdentityComponent A.hom P R
  let DB := picardIdentityComponent B.hom P' R'
  let DDA := picardIdentityComponent DA.hom Q S
  let DDB := picardIdentityComponent DB.hom Q' S'
  let hA : A ⟶ DDA := bidualMorphism A P R Q S
  let hB : B ⟶ DDB := bidualMorphism B P' R' Q' S'
  let fd : DB ⟶ DA := picardIdentityComponentPullback P R P' R' f
  let fdd : DDA ⟶ DDB := picardIdentityComponentPullback Q' S' Q S fd
  let ja : DDA ⟶ Q.obj := picardIdentityComponentι DA.hom Q S
  let jb : DDB ⟶ Q'.obj := picardIdentityComponentι DB.hom Q' S'
  let TA : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨A, LocallyOfFiniteType.isLocallyNoetherian A.hom⟩
  let qa : PicardGroup (pullback DA.hom A.hom) →+
      (fppfPicardSheaf DA.hom).obj.obj (op A) :=
    ((quotientProjection DA.hom ≫ toFppfPicardSheaf DA.hom).app (op A)).hom
  let qb : PicardGroup (pullback DB.hom A.hom) →+
      (fppfPicardSheaf DB.hom).obj.obj (op A) :=
    ((quotientProjection DB.hom ≫ toFppfPicardSheaf DB.hom).app (op A)).hom
  have ha : S.homEquiv (ObjectProperty.homMk (hA ≫ ja) : TA ⟶ Q) =
      qa (bidualFamilyClass A P R) := homEquiv_bidualMorphism A P R Q S
  have hb : S'.homEquiv (ObjectProperty.homMk ((f ≫ hB) ≫ jb) : TA ⟶ Q') =
      qb (pullbackClass ((familyScheme DB.hom).map f) (bidualFamilyClass B P' R')) :=
    homEquiv_comp_bidualMorphism B P' R' Q' S' (T := TA) f
  have hl := homEquiv_comp_picardIdentityComponentPullback Q' S' Q S fd (T := TA) hA
  change S'.homEquiv (ObjectProperty.homMk ((hA ≫ fdd) ≫ jb) : TA ⟶ Q') =
    ((fppfPicardPullback fd).hom.app (op A)).hom
      (S.homEquiv (ObjectProperty.homMk (hA ≫ ja) : TA ⟶ Q)) at hl
  change hA ≫ fdd = f ≫ hB
  apply (cancel_mono jb).mp
  suffices h : (ObjectProperty.homMk ((hA ≫ fdd) ≫ jb) : TA ⟶ Q') =
      ObjectProperty.homMk ((f ≫ hB) ≫ jb) from congrArg (fun q : TA ⟶ Q' => q.hom) h
  apply S'.homEquiv.injective
  calc
    _ = ((fppfPicardPullback fd).hom.app (op A)).hom
        (S.homEquiv (ObjectProperty.homMk (hA ≫ ja) : TA ⟶ Q)) := hl
    _ = ((fppfPicardPullback fd).hom.app (op A)).hom
        (qa (bidualFamilyClass A P R)) := by rw [ha]
    _ = qb (pullbackClass (familyMapOfHom fd A) (bidualFamilyClass A P R)) :=
      (fppfPicardPullback_class fd A (bidualFamilyClass A P R)).symm
    _ = qb (pullbackClass ((familyScheme DB.hom).map f) (bidualFamilyClass B P' R')) :=
      congrArg qb (bidualFamilyClass_sourcePullback A B P R P' R' f hf)
    _ = _ := hb.symm

/-- Native group maps supply their actual unit equation to the same whole
bidual naturality square. -/
theorem bidualMorphism_naturality_of_isMonHom (f : A ⟶ B) [IsMonHom f] :
    bidualMorphism A P R Q S ≫
      picardIdentityComponentPullback Q' S' Q S
        (picardIdentityComponentPullback P R P' R' f) =
      f ≫ bidualMorphism B P' R' Q' S' :=
  bidualMorphism_naturality A B P R P' R' Q S Q' S' f (IsMonHom.one_hom f)

end Naturality

section LineBundleComparison

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- The original normalized Mumford family class. Its bundle constructor
retains the source-unit evaluation factor before passing to classes. -/
def lineBundleDeltaClass (a : PicardGroup A.left) : PicardGroup (pullback A.hom A.hom) :=
  (normalizedFamilyClass A.hom η[A].left (Over.w η[A]) A
    (translationFamilyClass A (𝟙 A) a)).val

/-- Over a field the base pullback of the unit-fibre class is zero. This
is a class formula, not a deletion of that factor from the actual bundle. -/
theorem lineBundleDeltaClass_eq (a : PicardGroup A.left) :
    lineBundleDeltaClass A a =
      pullbackClass μ[A].left a - pullbackClass (fst A A).left a -
        pullbackClass (snd A A).left a := by
  rw [lineBundleDeltaClass, normalized_translationFamilyClass_val,
    translationFamilyClass_id, Over.id_left, pullbackClass_id]
  rfl

/-- Native commutativity makes the whole original normalized class symmetric. -/
theorem lineBundleDeltaClass_swap [IsCommMonObj A] (a : PicardGroup A.left) :
    pullbackClass (β_ A A).hom.left (lineBundleDeltaClass A a) =
      lineBundleDeltaClass A a := by
  have hm : (β_ A A).hom ≫ μ[A] = μ[A] := by
    have hmul : (fst A A) * (snd A A) = μ[A] := by
      rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    rw [← hmul, MonObj.comp_mul, braiding_hom_fst, braiding_hom_snd]
    exact _root_.mul_comm _ _
  rw [lineBundleDeltaClass_eq]
  simp only [← pullbackHom_apply, map_sub]
  simp only [pullbackHom_apply, ← pullbackClass_comp, ← Over.comp_left]
  rw [hm, braiding_hom_fst, braiding_hom_snd]
  abel

variable [IsProper A.hom] [GeometricallyIntegral A.hom]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf A.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The original Poincare pullback along phi_L is the EXISTING normalized
translated-family pair. Its literal normalization retains the unit-fibre
factor; no Poincare bundle on DA or geometry of DA is used. -/
def poincareLineBundleClassMorphismIso (L : LineBundle A.left) :
    RigidifiedPair.Iso
      (poincarePullback A P R
        (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)))
      (normalizedFamilyRigidifiedPair A.hom η[A].left (Over.w η[A]) A
        (translationFamilyLineBundle A (𝟙 A) L)) := by
  let TA : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨A, LocallyOfFiniteType.isLocallyNoetherian A.hom⟩
  let a := classOf A.left L
  let c := translationFamilyClass A (𝟙 A) a
  let q : PicardGroup (pullback A.hom A.hom) →+
      (fppfPicardSheaf A.hom).obj.obj (op A) :=
    ((quotientProjection A.hom ≫ toFppfPicardSheaf A.hom).app (op A)).hom
  refine poincarePullbackIsoOfFppfClass A P R (T := TA)
    (lineBundleClassMorphismIdentityComponent A P R a)
    (normalizedFamilyRigidifiedPair A.hom η[A].left (Over.w η[A]) A
      (translationFamilyLineBundle A (𝟙 A) L)) ?_
  rw [lineBundleClassMorphismIdentityComponent_ι]
  have h := fppf_homEquiv_comp_lineBundleClassMorphism A P R (T := TA) (𝟙 A) a
  rw [Category.id_comp] at h
  change R.homEquiv (ObjectProperty.homMk (lineBundleClassMorphism A P R a) : TA ⟶ P) =
    q c at h
  have hc : q (classOf _ (normalizedFamilyLineBundle A.hom η[A].left (Over.w η[A]) A
      (translationFamilyLineBundle A (𝟙 A) L))) = q c := by
    rw [classOf_normalizedFamilyLineBundle, classOf_translationFamilyLineBundle]
    exact fppfClass_normalizedFamilyClass_val A.hom η[A].left (Over.w η[A]) A c
  exact h.trans hc.symm

/-- The actual normalized comparison is unique under the original source geometry. -/
theorem poincareLineBundleClassMorphismIso_unique (L : LineBundle A.left)
    (e e' : RigidifiedPair.Iso
      (poincarePullback A P R
        (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)))
      (normalizedFamilyRigidifiedPair A.hom η[A].left (Over.w η[A]) A
        (translationFamilyLineBundle A (𝟙 A) L))) : e = e' :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    A.hom η[A].left (Over.w η[A]) _ _

/-- The original Poincare class pulled back along phi_L is the actual
normalized Mumford class, including its normalization convention. -/
theorem poincareClass_lineBundleClassMorphism_pullback (L : LineBundle A.left) :
    pullbackClass ((familyScheme A.hom).map
      (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)))
      (poincareClass A P R) = lineBundleDeltaClass A (classOf A.left L) := by
  let D := picardIdentityComponent A.hom P R
  let f : A ⟶ D := lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)
  let q : pullback A.hom A.hom ⟶ pullback A.hom D.hom := (familyScheme A.hom).map f
  have h : pullbackClass q (poincareClass A P R) =
      classOf _ (normalizedFamilyLineBundle A.hom η[A].left (Over.w η[A]) A
        (translationFamilyLineBundle A (𝟙 A) L)) := by
    change classOf (pullback A.hom A.hom)
        (pullbackLineBundle q (poincareLineBundle A P R)) = _
    exact Quotient.sound ⟨(poincareLineBundleClassMorphismIso A P R L).iso⟩
  rw [classOf_normalizedFamilyLineBundle, classOf_translationFamilyLineBundle] at h
  exact h

/-- Pulling the transposed original family back along phi_L gives the same
normalized class, by native commutativity of the ORIGINAL A. -/
theorem bidualFamilyClass_lineBundleClassMorphism_pullback (L : LineBundle A.left) :
    pullbackClass
      (familyMapOfHom (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)) A)
      (bidualFamilyClass A P R) = lineBundleDeltaClass A (classOf A.left L) := by
  let : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  rw [bidualFamilyClass, ← pullbackClass_comp]
  change pullbackClass
    (familyMapOfHom (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)) A ≫
      (β_ (picardIdentityComponent A.hom P R) A).hom.left) (poincareClass A P R) = _
  rw [familyMapOfHom_comp_swap, pullbackClass_comp,
    poincareClass_lineBundleClassMorphism_pullback, lineBundleDeltaClass_swap]

variable (Q : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType Q.obj.hom]
  (S : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf (picardIdentityComponent A.hom P R).hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)

/-- For every original line bundle, the original phi_L is its own dual
after the canonical bidual map. This proves the whole scheme-map equation,
without H1, geometry of DA, or a dual-isogeny degree assumption. -/
theorem bidualMorphism_comp_dual_lineBundleClassMorphism (L : LineBundle A.left) :
    bidualMorphism A P R Q S ≫
      picardIdentityComponentPullback P R Q S
        (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)) =
      lineBundleClassMorphismIdentityComponent A P R (classOf A.left L) := by
  let D := picardIdentityComponent A.hom P R
  let DD := picardIdentityComponent D.hom Q S
  let hA : A ⟶ DD := bidualMorphism A P R Q S
  let a := classOf A.left L
  let f : A ⟶ D := lineBundleClassMorphismIdentityComponent A P R a
  let fd : DD ⟶ D := picardIdentityComponentPullback P R Q S f
  let i : D ⟶ P.obj := picardIdentityComponentι A.hom P R
  let j : DD ⟶ Q.obj := picardIdentityComponentι D.hom Q S
  let TA : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨A, LocallyOfFiniteType.isLocallyNoetherian A.hom⟩
  let qa : PicardGroup (pullback A.hom A.hom) →+
      (fppfPicardSheaf A.hom).obj.obj (op A) :=
    ((quotientProjection A.hom ≫ toFppfPicardSheaf A.hom).app (op A)).hom
  let qd : PicardGroup (pullback D.hom A.hom) →+
      (fppfPicardSheaf D.hom).obj.obj (op A) :=
    ((quotientProjection D.hom ≫ toFppfPicardSheaf D.hom).app (op A)).hom
  have hh : S.homEquiv (ObjectProperty.homMk (hA ≫ j) : TA ⟶ Q) =
      qd (bidualFamilyClass A P R) := homEquiv_bidualMorphism A P R Q S
  have hf : R.homEquiv (ObjectProperty.homMk (f ≫ i) : TA ⟶ P) =
      qa (lineBundleDeltaClass A a) := by
    have h := fppf_homEquiv_comp_lineBundleClassMorphism A P R (T := TA) (𝟙 A) a
    rw [Category.id_comp] at h
    change R.homEquiv (ObjectProperty.homMk
      (lineBundleClassMorphism A P R a) : TA ⟶ P) =
      qa (translationFamilyClass A (𝟙 A) a) at h
    have hnorm : qa (lineBundleDeltaClass A a) =
        qa (translationFamilyClass A (𝟙 A) a) :=
      fppfClass_normalizedFamilyClass_val A.hom η[A].left (Over.w η[A]) A _
    change R.homEquiv (ObjectProperty.homMk
      (lineBundleClassMorphismIdentityComponent A P R a ≫
        picardIdentityComponentι A.hom P R) : TA ⟶ P) = _
    rw [lineBundleClassMorphismIdentityComponent_ι]
    exact h.trans hnorm.symm
  have hc := homEquiv_comp_picardIdentityComponentPullback P R Q S f (T := TA) hA
  change R.homEquiv (ObjectProperty.homMk ((hA ≫ fd) ≫ i) : TA ⟶ P) =
    ((fppfPicardPullback f).hom.app (op A)).hom
      (S.homEquiv (ObjectProperty.homMk (hA ≫ j) : TA ⟶ Q)) at hc
  change hA ≫ fd = f
  apply (cancel_mono i).mp
  suffices h : (ObjectProperty.homMk ((hA ≫ fd) ≫ i) : TA ⟶ P) =
      ObjectProperty.homMk (f ≫ i) from congrArg (fun q : TA ⟶ P => q.hom) h
  apply R.homEquiv.injective
  calc
    _ = ((fppfPicardPullback f).hom.app (op A)).hom
        (S.homEquiv (ObjectProperty.homMk (hA ≫ j) : TA ⟶ Q)) := hc
    _ = ((fppfPicardPullback f).hom.app (op A)).hom (qd (bidualFamilyClass A P R)) :=
      by rw [hh]
    _ = qa (pullbackClass (familyMapOfHom f A) (bidualFamilyClass A P R)) :=
      (fppfPicardPullback_class f A (bidualFamilyClass A P R)).symm
    _ = qa (lineBundleDeltaClass A a) :=
      congrArg qa (bidualFamilyClass_lineBundleClassMorphism_pullback A P R L)
    _ = _ := hf.symm

end LineBundleComparison

end AlgebraicGeometry.Scheme.RelativePicard
