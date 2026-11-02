/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.UniversalFamily
public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.Fppf

/-!
# The universal family on the original ordered divisor parameter

The degree-n universal pair, pulled back by the original based Abel map,
is rigidified-isomorphic to the existing normalized positive graph family.
The proof uses the equality of whole classifying morphisms and the original
rigidified/fppf comparison. It works on the entire parameter scheme before
specialization to points, and keeps every nonreduced test in the universal
classification boundary.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Scheme Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Abel.BoundedFamily

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
/-- The actual whole universal pullback and the original normalized graph
family are isomorphic as rigidified pairs. -/
theorem nonempty_degreeUniversalPair_orderedIso (n : ℕ) :
    letI := hX.smooth
    letI := hX.proper
    letI := picardCommGrpObj X.hom P R
    Nonempty (RigidifiedPair.Iso
      (RigidifiedPair.map (jacobianAbelMorphism hX o ho P R n)
        (degreeUniversalPair hX o ho P R n))
      (normalizedFamilyRigidifiedPair X.hom o ho (parameter X.hom n)
        (positiveFamilyLineBundle X.hom n))) := by
  let := hX.smooth
  let := hX.proper
  let := hX.flat
  let := hX.isGeometricallyIntegral
  let := picardCommGrpObj X.hom P R
  let T := locallyNoetherianParameter X n
  let U := RigidifiedPair.map (jacobianAbelMorphism hX o ho P R n)
    (degreeUniversalPair hX o ho P R n)
  let V := normalizedFamilyRigidifiedPair X.hom o ho (parameter X.hom n)
    (positiveFamilyLineBundle X.hom n)
  let c := classOf _ (positiveFamilyLineBundle X.hom n)
  let E := rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral X.hom o ho
  have hmap : jacobianAbelMorphism hX o ho P R n ≫ identityComponentι P.obj ≫
      (GrpObj.mulRight (picardPoint P R
        (n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)))).hom =
      (positiveAbelMorphism X P R n).hom := by
    rw [← Category.assoc, jacobianAbelMorphism_comp_inclusion]
    exact (positiveAbelMorphism_eq_based_comp_translation hX o ho P R n).symm
  have he : (ObjectProperty.homMk (jacobianAbelMorphism hX o ho P R n ≫
      identityComponentι P.obj ≫ (GrpObj.mulRight (picardPoint P R
        (n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)))).hom) : T ⟶ P) =
      positiveAbelMorphism X P R n := by
    ext : 1
    exact hmap
  have hU : (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T.obj)
      (classOf _ U.bundle) = positiveAbelSection X n :=
    (degreeUniversalPair_classifies hX o ho P R n (T := T)
      (jacobianAbelMorphism hX o ho P R n)).trans
        ((congrArg R.homEquiv he).trans (homEquiv_positiveAbelMorphism X P R n))
  have hn : (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T.obj)
      (classOf _ V.bundle) = positiveAbelSection X n := by
    have h₁ := normalizedFamilyClass_fppf X.hom o ho T.obj c
    have h₂ := normalizedFamilyClass_fppf X.hom o ho T.obj
      (normalizedFamilyClass X.hom o ho T.obj c).val
    rw [normalizedFamilyClass_normalized] at h₂
    have hc : classOf _ V.bundle = (normalizedFamilyClass X.hom o ho T.obj c).val :=
      classOf_normalizedFamilyLineBundle X.hom o ho T.obj _
    exact (congrArg (fun a : PicardGroup (pullback X.hom T.obj.hom) =>
      (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T.obj) a) hc).trans
        (h₂.symm.trans h₁)
  apply @Quotient.exact _ (RigidifiedPair.setoid (p := X.hom) (o := o) (ho := ho) T.obj) U V
  apply (E.app (op T.obj)).toEquiv.injective
  exact (rigidifiedPair_fppfClass X.hom o ho U).trans
    (hU.trans (hn.symm.trans (rigidifiedPair_fppfClass X.hom o ho V).symm))

/-- The comparison is an actual isomorphism of the original rigidified
bundles; it can be pulled back to every subsequent open or test scheme. -/
def degreeUniversalPairOrderedIso (n : ℕ) :
    letI := hX.smooth
    letI := hX.proper
    letI := picardCommGrpObj X.hom P R
    RigidifiedPair.Iso
      (RigidifiedPair.map (jacobianAbelMorphism hX o ho P R n)
        (degreeUniversalPair hX o ho P R n))
      (normalizedFamilyRigidifiedPair X.hom o ho (parameter X.hom n)
        (positiveFamilyLineBundle X.hom n)) :=
  Classical.choice (nonempty_degreeUniversalPair_orderedIso hX o ho P R n)

end AlgebraicGeometry.Scheme.OverField.Curve
