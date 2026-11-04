/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.IntrinsicComparison
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Cartier
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Isomorphism
public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Clopen

/-!
# The original positive theta image on the whole Picard scheme

The based theta ideal extends through the original translated clopen
component. The existing image comparison gives the ideal of the original
positive Abel image on the same Picard scheme. The origin is used only in
the proof, and no projective embedding or second image model is selected.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open Scheme Scheme.Modules Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Abel.BoundedFamily

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Properties X)
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- In positive genus the actual positive Abel image is effective Cartier
on the original whole Picard scheme, over algebraically closed constants. -/
theorem isEffectiveCartier_positiveAbelImage_of_isAlgClosed (hg : 0 < coherentGenus k X) :
    letI := hX.smooth
    letI := hX.proper
    Hom.IsEffectiveCartier
      (positiveAbelMorphism X P R (coherentGenus k X - 1)).hom.left.imageι := by
  let := hX.smooth
  let := hX.proper
  let := picardCommGrpObj X.hom P R
  let n := coherentGenus k X - 1
  obtain ⟨o, ho⟩ := hX.exists_rationalPoint_of_isAlgClosed
  let c := (identityComponentι P.obj).left
  have hc : IsClosed (Set.range c) := by
    change IsClosed (Set.range (identityComponent P.obj).ι)
    rw [Scheme.Opens.range_ι]
    exact (isClopen_identityComponent P.obj).isClosed
  let : IsClosedImmersion c :=
    { toSurjectiveOnStalks := inferInstance
      isClosedEmbedding :=
        { toIsEmbedding := c.isOpenEmbedding.isEmbedding, isClosed_range := hc } }
  let t := GrpObj.mulRight (picardPoint P R
    (n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)))
  let : IsIso t.hom.left := by
    change IsIso ((Over.forget (Spec (.of k))).map t.hom)
    infer_instance
  let u := c ≫ t.hom.left
  let j : basedAbelImage hX o ho P R n ⟶ (identityComponentOver P.obj).left :=
    (jacobianAbelMorphism hX o ho P R n).left.imageι
  let a : positiveAbelImage X P R n ⟶ P.obj.left :=
    (positiveAbelMorphism X P R n).hom.left.imageι
  have hj : Hom.IsEffectiveCartier j := isEffectiveCartier_basedAbelImage_pred hX o ho P R hg
  have hju : Hom.IsEffectiveCartier (j ≫ u) := Hom.isEffectiveCartier_comp_clopen j u hj
  let e := basedAbelImageIsoPositive hX o ho P R n
  have he : e.hom ≫ a = j ≫ u := basedAbelImageIsoPositive_hom_comp hX o ho P R n
  have hw : e.inv ≫ (j ≫ u) = a ≫ 𝟙 P.obj.left :=
    (congrArg (fun m : basedAbelImage hX o ho P R n ⟶ P.obj.left => e.inv ≫ m) he).symm.trans
      ((Iso.inv_hom_id_assoc e a).trans (Category.comp_id a).symm)
  let m := Hom.idealPullbackMap (j ≫ u) a (𝟙 P.obj.left) e.inv hw
  have hm : IsIso m :=
    Hom.idealPullbackMap_isIso_of_iso_square (j ≫ u) a (𝟙 P.obj.left) e.inv hw
  exact ⟨inferInstance, isLocallyRankOne_of_iso _
    (@asIso _ _ _ _ m hm)
    (pullback_locallyRankOne (𝟙 P.obj.left) _ hju.isLocallyRankOne)⟩

end AlgebraicGeometry.Scheme.OverField.Curve
