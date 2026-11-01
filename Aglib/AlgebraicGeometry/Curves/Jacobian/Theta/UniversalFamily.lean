/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.RankOneFamily
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.IntrinsicTranslation
public import Aglib.AlgebraicGeometry.Picard.Comparison.UniversalRigidified

/-!
# The same universal family on a translated Jacobian component

Pull the one existing universal rigidified pair on the supplied P/R back
along the original identity-component inclusion followed by translation by
n[O(o)]. The whole classifying formula and canonical composition isomorphism
precede all point evaluation. The resulting rank-one open uses the actual
cohomology and evaluation construction for relative curves.

This construction works over an arbitrary field with the displayed rational
origin. It does not assert that the chosen theta line bundle descends without
an origin, nor that the rank-one open is nonempty. The positive-genus
nonemptiness argument is supplied separately.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Scheme Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Group
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

/-- The original universal rigidified pair pulled back to the same Jacobian
after the positive degree-n translation. No new universal representative is chosen. -/
def degreeUniversalPair (n : ℕ) :
    letI := picardCommGrpObj X.hom P R
    RigidifiedPair X.hom o ho (identityComponentOver P.obj) := by
  let := picardCommGrpObj X.hom P R
  let := hX.proper
  let := hX.flat
  let := hX.isGeometricallyIntegral
  exact RigidifiedPair.map (identityComponentι P.obj ≫
    (GrpObj.mulRight (picardPoint P R
      (n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)))).hom)
    (fppfUniversalRigidifiedPair X.hom o ho R)

-- The same native family-map composition compares actual rigidified pairs.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The whole classifying identity on every represented test, including
nonreduced tests, for the original degree-n universal family. -/
theorem degreeUniversalPair_classifies (n : ℕ) :
    letI := picardCommGrpObj X.hom P R
    ∀ {T : LocallyNoetherianOver (Spec (.of k))} (a : T.obj ⟶ identityComponentOver P.obj),
      (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T.obj)
        (classOf _ (RigidifiedPair.map a (degreeUniversalPair hX o ho P R n)).bundle) =
      R.homEquiv (ObjectProperty.homMk (a ≫ identityComponentι P.obj ≫
        (GrpObj.mulRight (picardPoint P R
          (n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)))).hom)) := by
  let := picardCommGrpObj X.hom P R
  let := hX.proper
  let := hX.flat
  let := hX.isGeometricallyIntegral
  intro T a
  let b := identityComponentι P.obj ≫ (GrpObj.mulRight (picardPoint P R
    (n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)))).hom
  let Q := fppfUniversalRigidifiedPair X.hom o ho R
  have hc : classOf _ (RigidifiedPair.map a (degreeUniversalPair hX o ho P R n)).bundle =
      classOf _ (RigidifiedPair.map (a ≫ b) Q).bundle :=
    Quotient.sound ⟨(RigidifiedPair.mapCompIso a b Q).iso.symm⟩
  exact (congrArg (fun c : PicardGroup (pullback X.hom T.obj.hom) =>
    (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T.obj) c) hc).trans
      (fppfUniversalRigidifiedPullback_fppfClass X.hom o ho R
        (ObjectProperty.homMk (a ≫ b)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual rank-one cohomology open of that same universal family.
Nonemptiness and the degree of its evaluation divisor are not assumptions. -/
def degreeUniversalRankOneOpen (n : ℕ) :
    letI := picardCommGrpObj X.hom P R
    (identityComponentOver P.obj).left.Opens := by
  let := picardCommGrpObj X.hom P R
  let := hX.proper
  let := hX.smooth
  let := hX.connected
  letI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{u} 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have : SmoothOfRelativeDimension 1
      (pullback.snd X.hom (identityComponentOver P.obj).hom) :=
    MorphismProperty.pullback_snd _ _ hX.smooth
  have : IsLocallyNoetherian (identityComponentOver P.obj).left :=
    LocallyOfFiniteType.isLocallyNoetherian (identityComponentOver P.obj).hom
  exact Abel.rankOneOpen (pullback.snd X.hom (identityComponentOver P.obj).hom)
    (degreeUniversalPair hX o ho P R n).bundle

end AlgebraicGeometry.Scheme.OverField.Curve
