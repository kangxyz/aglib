/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.IntrinsicTranslation
public import Aglib.AlgebraicGeometry.Picard.BaseChangeGroupLaw

/-! The original represented constant Picard point under scalar extension. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory
open Scheme.RelativePicard Scheme.Modules.Invertible
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

attribute [local instance] Over.cartesianMonoidalCategory

private theorem pullbackClass_familyBaseChangeIso_inv_const
    {S S' Z : Scheme.{u}} (p : Z ⟶ S) (b : S' ⟶ S) (T : Over S')
    (c : PicardGroup Z) :
    pullbackClass (familyBaseChangeIso p b T).inv
        (pullbackClass (pullback.fst (pullback.snd p b) T.hom)
          (pullbackClass (pullback.fst p b) c)) =
      pullbackClass (pullback.fst p (T.hom ≫ b)) c := by
  let e := familyBaseChangeIso p b T
  let f := pullback.fst (pullback.snd p b) T.hom
  let g := pullback.fst p b
  let a := pullback.fst p (T.hom ≫ b)
  have h : e.hom ≫ a = f ≫ g := familyBaseChangeIso_hom_fst p b T
  have h' : e.inv ≫ (f ≫ g) = a := by
    rw [← h, e.inv_hom_id_assoc]
  calc
    _ = pullbackClass (e.inv ≫ (f ≫ g)) c := by
      rw [pullbackClass_comp, pullbackClass_comp]
    _ = _ := congrArg (fun q => pullbackClass q c) h'

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {X : FScheme k}
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The constant map represented by an original Picard class pulls back to
the constant map of the original pullback class. -/
theorem map_constant_picardPoint_fieldBaseChange
    (T : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType T.obj.hom]
    (c : PicardGroup X.left) :
    let b := Spec.algebraMap k K
    let F := Over.pullback b
    let P' := LocallyNoetherianOver.baseChange b P
    let R' := baseChangeRepresentableBy X.hom b P R
    let XK : FScheme K := Over.mk (pullback.snd X.hom b)
    let d : 𝟙_ (FScheme K) ⟶ P'.obj :=
      picardPoint (X := XK) P' R' (pullbackClass (pullback.fst X.hom b) c)
    F.map (toUnit T.obj ≫ picardPoint (X := X) P R c) = toUnit (F.obj T.obj) ≫ d := by
  let b := Spec.algebraMap k K
  let F := Over.pullback b
  let T' := LocallyNoetherianOver.baseChange b T
  let T₀ := (LocallyNoetherianOver.map b).obj T'
  let P' := LocallyNoetherianOver.baseChange b P
  let R' := baseChangeRepresentableBy X.hom b P R
  let XK : FScheme K := Over.mk (pullback.snd X.hom b)
  let adj := Over.mapPullbackAdj b
  let E := fppfPicardSheafBaseChangeIso X.hom b
  let cK := pullbackClass (pullback.fst X.hom b) c
  let c₀ := pullbackClass (pullback.fst X.hom T₀.obj.hom) c
  let c' := pullbackClass (pullback.fst XK.hom T'.obj.hom) cK
  let q₀ := (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T₀.obj)
  let q₁ := (quotientProjection XK.hom ≫ toFppfPicardSheaf XK.hom).app (op T'.obj)
  let f : T' ⟶ P' := ObjectProperty.homMk (F.map (toUnit T.obj ≫ picardPoint P R c))
  let f' : T' ⟶ P' := ObjectProperty.homMk (toUnit T'.obj ≫ picardPoint (X := XK) P' R' cK)
  have hd : (adj.homEquiv T'.obj P.obj).symm f.hom = toUnit T₀.obj ≫ picardPoint P R c := by
    change (adj.homEquiv T'.obj P.obj).symm (F.map (toUnit T.obj ≫ picardPoint P R c)) = _
    rw [F.map_comp, adj.homEquiv_naturality_right_symm]
    exact congrArg (fun a : T₀.obj ⟶ 𝟙_ (FScheme k) => a ≫ picardPoint P R c)
      (toUnit_unique _ _)
  have hleft : (E.hom.app (op T'.obj)).hom (R'.homEquiv f) = q₀ c₀ := by
    have h := baseChangeRepresentableBy_homEquiv X.hom b P R (T := T') f
    change R'.homEquiv f = (E.inv.app (op T'.obj)).hom
      (R.homEquiv (ObjectProperty.homMk ((adj.homEquiv T'.obj P.obj).symm f.hom) : T₀ ⟶ P)) at h
    rw [h, hd, Abel.BoundedFamily.homEquiv_constant_picardPoint (X := X) P R T₀ c]
    exact fppfPicardSheafBaseChangeIso_hom_app_inv_app_apply X.hom b (q₀ c₀)
  let e := familyBaseChangeIso X.hom b T'.obj
  have hc' : pullbackClass e.inv c' = c₀ :=
    pullbackClass_familyBaseChangeIso_inv_const X.hom b T'.obj c
  have hright : (E.hom.app (op T'.obj)).hom (R'.homEquiv f') = q₀ c₀ := by
    have hval : R'.homEquiv f' = q₁ c' :=
      Abel.BoundedFamily.homEquiv_constant_picardPoint (X := XK) P' R' T' cK
    rw [hval]
    have h := fppfPicardSheafBaseChangeIso_hom_app_toFppfPicardSheaf_mk X.hom b (op T'.obj) c'
    change (E.hom.app (op T'.obj)).hom (q₁ c') = q₀ (pullbackClass e.inv c') at h
    exact h.trans (congrArg q₀ hc')
  have h : f = f' := by
    apply R'.homEquiv.injective
    apply (E.app (op T'.obj)).addCommGroupIsoToAddEquiv.injective
    exact hleft.trans hright.symm
  exact congrArg (fun g : T' ⟶ P' => g.hom) h

private theorem map_mul_of_grpObj_eq
    {C D : Type*} [Category C] [Category D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] {G T : C} [GrpObj G]
    (N : GrpObj (F.obj G)) (hN : N = Functor.grpObjObj (F := F) (G := G))
    (a d : T ⟶ G) :
    letI : GrpObj (F.obj G) := N
    F.map (a * d) = F.map a * F.map d := by
  cases hN
  exact F.map_mul a d

/-- The original translation on the original Picard scheme commutes with
field extension and the same positive class pullback. -/
theorem map_picardTranslation_fieldBaseChange (c : PicardGroup X.left) :
    let b := Spec.algebraMap k K
    let F := Over.pullback b
    let P' := LocallyNoetherianOver.baseChange b P
    let R' := baseChangeRepresentableBy X.hom b P R
    let XK : FScheme K := Over.mk (pullback.snd X.hom b)
    letI := picardCommGrpObj X.hom P R
    letI := picardCommGrpObj XK.hom P' R'
    let d : 𝟙_ (FScheme K) ⟶ P'.obj :=
      picardPoint (X := XK) P' R' (pullbackClass (pullback.fst X.hom b) c)
    F.map (GrpObj.mulRight (picardPoint (X := X) P R c)).hom = (GrpObj.mulRight d).hom := by
  let b := Spec.algebraMap k K
  let F := Over.pullback b
  let P' := LocallyNoetherianOver.baseChange b P
  let R' := baseChangeRepresentableBy X.hom b P R
  let := picardCommGrpObj X.hom P R
  let XK : FScheme K := Over.mk (pullback.snd X.hom b)
  let N := picardCommGrpObj XK.hom P' R'
  let : GrpObj P'.obj := N.toGrpObj
  let cK := pullbackClass (pullback.fst X.hom b) c
  let d := toUnit P.obj ≫ picardPoint P R c
  have h := map_mul_of_grpObj_eq F N.toGrpObj
    (picardCommGrpObj_baseChange_toGrpObj X.hom b P R) (𝟙 P.obj) d
  change F.map ((𝟙 P.obj) * d) =
    (𝟙 P'.obj) * (toUnit P'.obj ≫ picardPoint (X := XK) P' R' cK)
  calc
    _ = F.map (𝟙 P.obj) * F.map d := h
    _ = _ := by
      rw [F.map_id]
      exact congrArg (fun a : P'.obj ⟶ P'.obj => (𝟙 P'.obj) * a)
        (map_constant_picardPoint_fieldBaseChange (K := K) P R P c)

end AlgebraicGeometry.Scheme.OverField.Curve
