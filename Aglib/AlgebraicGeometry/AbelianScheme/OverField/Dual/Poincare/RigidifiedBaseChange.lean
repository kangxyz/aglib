/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Poincare.FieldBaseChange
public import Aglib.AlgebraicGeometry.Group.BaseChange.MarkedKernel
public import Aglib.AlgebraicGeometry.Picard.Comparison.Rigidified.FamilyPullback
public import Aglib.AlgebraicGeometry.Picard.Scheme.IdentityComponentBaseChangeGroup

/-! Scalar extension of the original normalized Poincare pair. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj Opposite
open Scheme.OverField Scheme.Cohomology Scheme.Group Scheme.Modules.Invertible
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (A : Grp (FScheme k))
  [IsProper A.X.hom] [GeometricallyIntegral A.X.hom]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  (K : Type u) [Field K] [Algebra k K]

/-- The original Poincare pullback, transported to the original
scalar-extended family with its original lifted group unit. -/
def poincarePullbackOnFieldBaseChange
    (T : LocallyNoetherianOver (Spec (.of K)))
    (t : T.obj ⟶ fieldBaseChange K (picardIdentityComponent A.X.hom P R)) :
    let b := Spec.algebraMap k K
    let B := ((Over.pullback b).mapGrp.obj A).X
    RigidifiedPair B.hom η[B].left (Over.w η[B]) T.obj := by
  let b := Spec.algebraMap k K
  let B := ((Over.pullback b).mapGrp.obj A).X
  let T₀ := (LocallyNoetherianOver.map b).obj T
  let d : T₀.obj ⟶ picardIdentityComponent A.X.hom P R :=
    ((Over.mapPullbackAdj b).homEquiv T.obj _).symm t
  let o := η[A.X].left
  let ho := Over.w η[A.X]
  let e : pullback B.hom T.obj.hom ≅ pullback A.X.hom T₀.obj.hom :=
    familyBaseChangeIso A.X.hom b T.obj
  let v := originSection A.X.hom o ho (Over.mk b)
  have hv : η[B].left = v := Group.BaseChange.origin_eq_lift b A
  let a := originSection B.hom η[B].left (Over.w η[B]) T.obj
  let hV := originSection_snd A.X.hom o ho (Over.mk b)
  let z : T.obj.left ⟶ pullback B.hom T.obj.hom :=
    originSection (pullback.snd A.X.hom b) v hV T.obj
  have ht : a = z := by
    apply pullback.hom_ext
    · have h₁ : a ≫ pullback.fst B.hom T.obj.hom = T.obj.hom ≫ η[B].left :=
        originSection_fst B.hom η[B].left (Over.w η[B]) T.obj
      have h₂ : z ≫ pullback.fst B.hom T.obj.hom = T.obj.hom ≫ v :=
        originSection_fst (pullback.snd A.X.hom b) v hV T.obj
      exact h₁.trans ((congrArg (fun q => T.obj.hom ≫ q) hv).trans h₂.symm)
    · have h₁ : a ≫ pullback.snd B.hom T.obj.hom = 𝟙 _ :=
        originSection_snd B.hom η[B].left (Over.w η[B]) T.obj
      have h₂ : z ≫ pullback.snd B.hom T.obj.hom = 𝟙 _ :=
        originSection_snd (pullback.snd A.X.hom b) v hV T.obj
      exact h₁.trans h₂.symm
  have h : originSection B.hom η[B].left (Over.w η[B]) T.obj ≫ e.hom =
      (𝟙 T.obj.left) ≫ originSection A.X.hom o ho T₀.obj :=
    (congrArg (fun a => a ≫ e.hom) ht).trans
      ((RigidifiedPair.originSection_comp_familyBaseChangeIso (ho := ho) b T.obj).trans
        (Category.id_comp _).symm)
  exact RigidifiedPair.mapFamily
    (p := A.X.hom) (o := o) (ho := ho) (T := T₀.obj)
    (p' := B.hom) (o' := η[B].left) (ho' := Over.w η[B]) (T' := T.obj)
    e.hom (𝟙 T.obj.left) h (poincarePullback A.X P R d)

/-- The same original normalized Poincare pair commutes with field
extension on the represented tests, using the actual Picard component
comparison and the original family isomorphism. -/
def poincarePullbackFieldBaseChangeIso
    (T : LocallyNoetherianOver (Spec (.of K)))
    (t : T.obj ⟶ fieldBaseChange K (picardIdentityComponent A.X.hom P R)) :
    let b := Spec.algebraMap k K
    let B := ((Over.pullback b).mapGrp.obj A).X
    let P' := LocallyNoetherianOver.baseChange b P
    let R' := baseChangeRepresentableBy A.X.hom b P R
    let D := picardIdentityComponent A.X.hom P R
    let D' := picardIdentityComponent B.hom P' R'
    let e : fieldBaseChange K D ≅ D' := picardIdentityComponentBaseChangeOverIso P R K
    letI : IsProper B.hom := inferInstanceAs (IsProper (pullback.snd A.X.hom b))
    letI : GeometricallyIntegral B.hom :=
      inferInstanceAs (GeometricallyIntegral (pullback.snd A.X.hom b))
    letI : LocallyOfFiniteType P'.obj.hom :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd P.obj.hom b))
    RigidifiedPair.Iso (poincarePullback B P' R' (t ≫ e.hom))
      (poincarePullbackOnFieldBaseChange A P R K T t) := by
  let b := Spec.algebraMap k K
  let B := ((Over.pullback b).mapGrp.obj A).X
  let P' := LocallyNoetherianOver.baseChange b P
  let R' := baseChangeRepresentableBy A.X.hom b P R
  let D := picardIdentityComponent A.X.hom P R
  let D' := picardIdentityComponent B.hom P' R'
  let e : fieldBaseChange K D ≅ D' := picardIdentityComponentBaseChangeOverIso P R K
  let : IsProper B.hom := inferInstanceAs (IsProper (pullback.snd A.X.hom b))
  let : GeometricallyIntegral B.hom :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd A.X.hom b))
  let : LocallyOfFiniteType P'.obj.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd P.obj.hom b))
  let T₀ := (LocallyNoetherianOver.map b).obj T
  let d : T₀.obj ⟶ D := ((Over.mapPullbackAdj b).homEquiv T.obj D).symm t
  let M := poincarePullbackOnFieldBaseChange A P R K T t
  let u := t ≫ e.hom
  let c := pullbackClass ((familyScheme A.X.hom).map d) (poincareClass A.X P R)
  let eF : pullback B.hom T.obj.hom ≅ pullback A.X.hom T₀.obj.hom :=
    familyBaseChangeIso A.X.hom b T.obj
  let q := (quotientProjection B.hom ≫ toFppfPicardSheaf B.hom).app (op T.obj)
  have hm : classOf _ M.bundle = pullbackClass eF.hom c := by
    unfold M c poincarePullbackOnFieldBaseChange RigidifiedPair.mapFamily
      poincarePullback poincareClass
    rfl
  have hC := poincareClass_fieldBaseChange A.X P R K T t
  have hM := fppfPicardClass_fieldBaseChange A.X K T.obj c
  have hU := poincarePullback_fppfClass B P' R' (T := T) u
  have h := hU.symm.trans (hC.symm.trans hM)
  exact poincarePullbackIsoOfFppfClass B P' R' (T := T) u M
    (h.trans (congrArg q hm.symm))

end AlgebraicGeometry.Scheme.RelativePicard
