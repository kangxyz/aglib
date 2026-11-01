/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.IncidenceEquality
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.EvaluationClass
public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.SourcePullback

/-!
# The original difference family as a relative Picard class

Apply the whole arbitrary-source translation law to the original based
Abel curve map and the original theta line bundle. The actual divisor
equality identifies its positive part with the original evaluation family.
The remaining coefficient is the global line-bundle pullback along the
original Abel map; no Cartier pullback along that map is made. Passing to
the relative Picard sheaf gives the original degree-g classifying equation
minus that fixed coefficient on the entire retained open.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open Opposite AlgebraicGeometry Scheme Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The entire pulled-back translation class on the original X times V.
The coefficient inversion and parameter inversion retain their distinct roles. -/
theorem theta_sourcePullback_translationClass (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    let J := identityComponentOver P.obj
    let V := thetaParameterOver hX o ho P R
    let a := classOf J.left (thetaLineBundle hX o ho P R hg)
    pullbackClass (familyMapOfHom (jacobianCurveMorphism hX o ho P R) V)
        (translationFamilyClass J (thetaParameterι hX o ho P R ≫ ι[J])
          (pullbackClass ι[J].left a)) =
      classOf _ (thetaEvaluationPositiveLineBundle hX o ho P R) -
        pullbackClass (pullback.fst X.hom V.hom)
          (pullbackClass (jacobianCurveMorphism hX o ho P R).left
            (pullbackClass ι[J].left a)) := by
  let := picardCommGrpObj X.hom P R
  dsimp only
  rw [pullbackClass_familyMapOfHom_translationFamilyClass_inv,
    ← thetaIncidenceDifference_eq, thetaEvaluation_positiveClass_eq]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same whole class in the original relative Picard sheaf, with
the original degree-g classifier and the fixed source coefficient explicit. -/
theorem theta_sourcePullback_translationFppfClass (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    let J := identityComponentOver P.obj
    let V := thetaParameterOver hX o ho P R
    let T : LocallyNoetherianOver (Spec (.of k)) :=
      ⟨V, thetaParameter_isLocallyNoetherian hX o ho P R⟩
    let a := classOf J.left (thetaLineBundle hX o ho P R hg)
    let q := (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op V)
    q (pullbackClass (familyMapOfHom (jacobianCurveMorphism hX o ho P R) V)
      (translationFamilyClass J (thetaParameterι hX o ho P R ≫ ι[J])
        (pullbackClass ι[J].left a))) =
      Sub.sub (α := (fppfPicardSheaf X.hom).obj.obj (op V))
        (R.homEquiv (ObjectProperty.homMk (thetaParameterι hX o ho P R ≫
        identityComponentι P.obj ≫ (GrpObj.mulRight (picardPoint P R
          (coherentGenus k X • classOf X.left
            (PointDivisor.positiveLineBundle X hX o ho)))).hom) : T ⟶ P))
        (q (pullbackClass (pullback.fst X.hom V.hom)
          (pullbackClass (jacobianCurveMorphism hX o ho P R).left
            (pullbackClass ι[J].left a)))) := by
  let := picardCommGrpObj X.hom P R
  dsimp only
  rw [theta_sourcePullback_translationClass, map_sub]
  exact congrArg₂ (Sub.sub (α := (fppfPicardSheaf X.hom).obj.obj
    (op (thetaParameterOver hX o ho P R))))
    (thetaEvaluation_fppfClass hX o ho P R) rfl

end AlgebraicGeometry.Scheme.OverField.Curve
