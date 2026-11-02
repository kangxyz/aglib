/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.DegreeZero
public import Aglib.AlgebraicGeometry.Picard.Scheme.IdentityComponentBaseChangeMap
public import Aglib.AlgebraicGeometry.Picard.Scheme.IdentityComponentQuasiProjective
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# Projectivity of the same Jacobian over any field

The actual identity component of the supplied locally Noetherian Picard representative is
H-quasi-projective over the ground field by the general Picard theorem. Its properness follows
by base-changing the same curve and representative to the algebraic closure, applying the
algebraically closed properness theorem, and transporting through the actual native component
comparison with its proved structure-map triangle. Universally closed descends fpqc; the
original component is already separated and locally of finite type. Proper plus
H-quasi-projective then gives H-projective over the original field.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Group
open AlgebraicGeometry.Scheme.RelativePicard

namespace AlgebraicGeometry.Scheme.OverField.Curve

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

include hX in
/-- The actual Jacobian of a smooth proper geometrically connected curve is H-quasi-projective
over every field, for the supplied Picard representative. -/
theorem isHQuasiProjective_identityComponentOver :
    letI := picardCommGrpObj X.hom P R
    IsHQuasiProjective (identityComponentOver P.obj).hom := by
  obtain ⟨N, i, hi, hiX⟩ := hX.exists_closedImmersion_projectiveSpace
  have hflat := hX.flat
  have hgi := hX.isGeometricallyIntegral
  obtain ⟨Xl, ⟨⟨⟩⟩, Xh⟩ := X
  change Xl ⟶ ProjectiveSpace k (ULift.{u} (Fin (N + 1))) at i
  change i ≫ ProjectiveSpace.toSpec k (ULift.{u} (Fin (N + 1))) = Xh at hiX
  subst hiX
  have : Flat (i ≫ ProjectiveSpace.toSpec k (ULift.{u} (Fin (N + 1)))) := hflat
  have : GeometricallyIntegral (i ≫ ProjectiveSpace.toSpec k (ULift.{u} (Fin (N + 1)))) := hgi
  exact isHQuasiProjective_picardIdentityComponent_hom i Equiv.ulift P R

variable [IsSeparated P.obj.hom]

include hX in
/-- The actual Jacobian is proper over every ground field. Properness of its same base-changed
identity component descends from the algebraic closure along the original fpqc field map. -/
theorem isProper_identityComponentOver :
    letI := picardCommGrpObj X.hom P R
    IsProper (identityComponentOver P.obj).hom := by
  let := picardCommGrpObj X.hom P R
  let K := AlgebraicClosure k
  let b : Spec (.of K) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  let P' := LocallyNoetherianOver.baseChange b P
  let R' := baseChangeRepresentableBy X.hom b P R
  let J := picardIdentityComponent X.hom P R
  change IsProper J.hom
  have : IsSeparated J.hom := by
    change IsSeparated ((identityComponent P.obj).ι ≫ P.obj.hom)
    infer_instance
  have : IsSeparated P'.obj.hom := by
    change IsSeparated (pullback.snd P.obj.hom b)
    infer_instance
  have hproper : IsProper
      (picardIdentityComponent (pullback.snd X.hom b) P' R').hom :=
    isProper_identityComponentOver_of_isAlgClosed (curveProperties_baseChange hX K b) P' R'
  have : IsProper (pullback.snd J.hom b) := by
    rw [← picardIdentityComponentBaseChangeIso_hom_comp X.hom P R K]
    infer_instance
  have : Flat b := by
    apply Flat.SpecMap_iff.mpr
    change (algebraMap k K).Flat
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have : Surjective b := ⟨Function.surjective_to_subsingleton _⟩
  have : QuasiCompact b := quasiCompact_of_compactSpace b
  have : UniversallyClosed J.hom :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := J.hom) (g := b)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  exact ⟨⟩

include hX in
/-- The same chosen Jacobian is H-projective over every ground field: its properness is
descended, and its quasi-projectivity is supplied directly over that field. -/
theorem isHProjective_identityComponentOver :
    letI := picardCommGrpObj X.hom P R
    IsHProjective (identityComponentOver P.obj).hom := by
  let := picardCommGrpObj X.hom P R
  have := isProper_identityComponentOver hX P R
  have := isHQuasiProjective_identityComponentOver hX P R
  exact IsHProjective.of_isHQuasiProjective_of_isProper _

end AlgebraicGeometry.Scheme.OverField.Curve
