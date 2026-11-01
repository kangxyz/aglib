/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.IntrinsicTranslation
public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.ClosedIdentification
public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.Dominance
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# The original positive image and the based image

The same ordered parameter scheme is schematically dense in both actual
images. The whole positive/based translation identity therefore identifies
their original kernel ideals inside the same Picard scheme. The resulting
isomorphism preserves both the ambient maps and the original parameter map;
it does not replace either image by a reduced support.

Identification of the ambient translated component with the intrinsic
degree stratum is a separate statement. No degree-stratum identification or
Hilbert image comparison is assumed here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Scheme Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]

-- Preserve the actual original product-object and component-map presentations.
omit [IsSeparated P.obj.hom] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original positive and based maps, including their component inclusion,
are related by the native translation isomorphism. -/
theorem jacobianAbelMorphism_comp_translation (n : ℕ) :
    letI := picardCommGrpObj X.hom P R
    (jacobianAbelMorphism hX o ho P R n).left ≫ (identityComponentι P.obj).left ≫
      (GrpObj.mulRight (picardPoint P R
        (n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)))).hom.left =
      (positiveAbelMorphism X P R n).hom.left := by
  let := picardCommGrpObj X.hom P R
  have h := congrArg Over.Hom.left
    (jacobianAbelMorphism_comp_inclusion hX o ho P R n)
  rw [← Category.assoc, ← Over.comp_left, h]
  exact (congrArg Over.Hom.left
    (positiveAbelMorphism_eq_based_comp_translation hX o ho P R n)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual image isomorphism produced by their common schematically
dense source, before any specialization to points. -/
def basedAbelImageIsoPositive (n : ℕ) :
    basedAbelImage hX o ho P R n ≅ positiveAbelImage X P R n := by
  let := picardCommGrpObj X.hom P R
  let f := (jacobianAbelMorphism hX o ho P R n).left
  let g := (positiveAbelMorphism X P R n).hom.left
  let τ := (GrpObj.mulRight (picardPoint P R
    (n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)))).hom.left
  have : IsClosedImmersion (identityComponentι P.obj).left :=
    IsClosedImmersion.of_isPreimmersion _ (by
      change IsClosed (Set.range (identityComponent P.obj).ι)
      rw [Scheme.Opens.range_ι]
      exact isClosed_identityComponent P.obj)
  have : IsProper f := isProper_jacobianAbelMorphism hX o ho P R n
  have : IsProper g := isProper_positiveAbelMorphism X P R n
  have : IsSchemeTheoreticallyDominant f.toImage := isSchemeTheoreticallyDominant_toImage f
  have : IsSchemeTheoreticallyDominant g.toImage := isSchemeTheoreticallyDominant_toImage g
  exact closedIsoOfCommonDenseSource
    (f.imageι ≫ (identityComponentι P.obj).left ≫ τ) g.imageι f.toImage g.toImage (by
      simp only [Hom.toImage_imageι, Hom.toImage_imageι_assoc]
      exact jacobianAbelMorphism_comp_translation hX o ho P R n)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The image isomorphism preserves the exact translated ambient inclusion. -/
theorem basedAbelImageIsoPositive_hom_comp (n : ℕ) :
    letI := picardCommGrpObj X.hom P R
    (basedAbelImageIsoPositive hX o ho P R n).hom ≫
      (positiveAbelMorphism X P R n).hom.left.imageι =
      (jacobianAbelMorphism hX o ho P R n).left.imageι ≫
        (identityComponentι P.obj).left ≫ (GrpObj.mulRight (picardPoint P R
          (n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)))).hom.left := by
  let := picardCommGrpObj X.hom P R
  exact IsClosedImmersion.lift_fac _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The image isomorphism also preserves the original ordered parameter map. -/
theorem toImage_basedAbelImageIsoPositive (n : ℕ) :
    (jacobianAbelMorphism hX o ho P R n).left.toImage ≫
      (basedAbelImageIsoPositive hX o ho P R n).hom =
      (positiveAbelMorphism X P R n).hom.left.toImage := by
  let := picardCommGrpObj X.hom P R
  apply (cancel_mono (positiveAbelMorphism X P R n).hom.left.imageι).mp
  rw [Category.assoc, basedAbelImageIsoPositive_hom_comp,
    Hom.toImage_imageι_assoc, Hom.toImage_imageι]
  exact jacobianAbelMorphism_comp_translation hX o ho P R n

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
