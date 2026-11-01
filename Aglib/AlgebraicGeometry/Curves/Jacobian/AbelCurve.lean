/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.AbelGeometry

/-!
# The original based Abel morphism from the curve to its Jacobian

Lift the identity coordinate of the original curve to the existing
one-coordinate parameter, then apply the existing based degree-one Abel
morphism into the same supplied Picard representative's identity component.
The whole factorization and classifying formula on all represented locally
Noetherian tests precede the
pointed equation f(o)=unit. The class is [q-o], with no sign change and no
new curve, divisor parameter, Picard representative, or Jacobian model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Scheme Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Abel.BoundedFamily

variable {k : Type u} [Field k]

/-- The canonical one-coordinate lift of the original curve over its
original base. Its source is the original object X. -/
def singleParameterMorphism (X : FScheme k) : X ⟶ parameter X.hom 1 :=
  finiteProductOverLift (T := X) (fun _ : Fin 1 => Over.mk X.hom)
    (fun _ => Over.homMk (𝟙 X.left) (Category.id_comp _))

/-- The original coordinate of the one-coordinate lift is the identity. -/
theorem singleParameterMorphism_coordinate (X : FScheme k) (i : Fin 1) :
    (singleParameterMorphism X).left ≫ coordinate X.hom 1 i = 𝟙 X.left :=
  congrArg Over.Hom.left (finiteProductOverLift_π (T := X)
    (fun _ : Fin 1 => Over.mk X.hom)
    (fun _ => Over.homMk (𝟙 X.left) (Category.id_comp _)) i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The identity-coordinate lift commutes with every original test map. -/
theorem comp_singleParameterMorphism (X : FScheme k) {T : Over (Spec (.of k))}
    (q : T ⟶ X) :
    q ≫ singleParameterMorphism X =
      Over.homMk (parameterPoint X.hom T.hom (fun _ : Fin 1 => q.left) (fun _ => q.w))
        (parameterPoint_over X.hom T.hom _ _) := by
  apply finiteProductOver_hom_ext
  intro i
  apply Over.OverMorphism.ext
  change (q.left ≫ (singleParameterMorphism X).left) ≫ coordinate X.hom 1 i =
    parameterPoint X.hom T.hom (fun _ : Fin 1 => q.left) (fun _ => q.w) ≫
      coordinate X.hom 1 i
  rw [Category.assoc, singleParameterMorphism_coordinate, Category.comp_id,
    parameterPoint_coordinate]

variable {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom]

/-- The original based Abel curve morphism f_o:X→J, using the existing
ordered one-point family and the same identity-component factorization. -/
def jacobianCurveMorphism :
    letI := picardCommGrpObj X.hom P R
    X ⟶ identityComponentOver P.obj := by
  let := picardCommGrpObj X.hom P R
  exact singleParameterMorphism X ≫ jacobianAbelMorphism hX o ho P R 1

/-- The actual Abel curve map retains its original map into P. -/
theorem jacobianCurveMorphism_comp_inclusion :
    letI := hX.smooth
    letI := hX.proper
    letI := picardCommGrpObj X.hom P R
    jacobianCurveMorphism hX o ho P R ≫ identityComponentι P.obj =
      singleParameterMorphism X ≫ (abelMorphism o ho P R 1).hom := by
  let := hX.smooth
  let := hX.proper
  let := picardCommGrpObj X.hom P R
  change (singleParameterMorphism X ≫ jacobianAbelMorphism hX o ho P R 1) ≫
    identityComponentι P.obj = _
  rw [Category.assoc, jacobianAbelMorphism_comp_inclusion]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On every represented test, including nonreduced tests, the original
curve morphism classifies the actual graph difference [q-o]. -/
theorem homEquiv_comp_jacobianCurveMorphism :
    letI := hX.smooth
    letI := hX.proper
    letI := picardCommGrpObj X.hom P R
    ∀ {T : LocallyNoetherianOver (Spec (.of k))} (q : T.obj ⟶ X),
      R.homEquiv (ObjectProperty.homMk
        (q ≫ jacobianCurveMorphism hX o ho P R ≫ identityComponentι P.obj)) =
      (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T.obj)
        (Hom.abelClass Hom.smoothRelativeDivisorIdeal X.hom o ho T.obj.hom q.left q.w) := by
  let := hX.smooth
  let := hX.proper
  let := picardCommGrpObj X.hom P R
  intro T q
  have he : (ObjectProperty.homMk
      (q ≫ jacobianCurveMorphism hX o ho P R ≫ identityComponentι P.obj) : T ⟶ P) =
      (ObjectProperty.homMk
        (Over.homMk (parameterPoint X.hom T.obj.hom (fun _ : Fin 1 => q.left) (fun _ => q.w))
          (parameterPoint_over X.hom T.obj.hom _ _) : T.obj ⟶ parameter X.hom 1) :
          T ⟶ locallyNoetherianParameter X 1) ≫ abelMorphism o ho P R 1 := by
    ext : 1
    rw [jacobianCurveMorphism_comp_inclusion, ← Category.assoc, comp_singleParameterMorphism]
    rfl
  exact (congrArg R.homEquiv he).trans (by
    simpa only [Fin.sum_univ_one] using
      homEquiv_parameterPoint_comp_abelMorphism o ho P R (T := T)
        (fun _ : Fin 1 => q.left) (fun _ => q.w))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The based Abel curve map sends the given original rational point to
the original group unit, as an equality of morphisms over k. -/
theorem jacobianCurveMorphism_pointed :
    letI := picardCommGrpObj X.hom P R
    (Over.homMk o ho : 𝟙_ (Over (Spec (.of k))) ⟶ X) ≫
      jacobianCurveMorphism hX o ho P R = η[identityComponentOver P.obj] := by
  let := hX.smooth
  let := hX.proper
  let := picardCommGrpObj X.hom P R
  have horigin : (Over.homMk o ho : 𝟙_ (Over (Spec (.of k))) ⟶ X) ≫
      singleParameterMorphism X = originPoint o ho 1 :=
    comp_singleParameterMorphism X (T := 𝟙_ (Over (Spec (.of k))))
      (Over.homMk o ho : 𝟙_ (Over (Spec (.of k))) ⟶ X)
  apply (cancel_mono (identityComponentι P.obj)).mp
  rw [Category.assoc, jacobianCurveMorphism_comp_inclusion, ← Category.assoc, horigin,
    originPoint_comp_abelMorphism, one_identityComponentOver, identityComponentOne_ι]

end AlgebraicGeometry.Scheme.OverField.Curve
