/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Descent.BasedCartier
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Descent.ConstantPicardBaseChange
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Descent.FieldComparison
public import Aglib.AlgebraicGeometry.Curves.PointDivisor.PositiveBaseChange

/-! The original based theta class under the original Jacobian scalar extension. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Scheme.RelativePicard Scheme.Cohomology Scheme.Modules.Invertible
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The original based theta class after any field extension is the original
based theta class for the lifted origin, along the native component iso. -/
theorem pullbackClass_thetaLineBundleGroundField_fieldBaseChange
    (K : Type u) [Field K] [Algebra k K] (hg : 0 < coherentGenus k X) :
    let b := Spec.algebraMap k K
    let XK := fieldBaseChange K X
    let PK := LocallyNoetherianOver.baseChange b P
    let RK := baseChangeRepresentableBy X.hom b P R
    let hXK := curveProperties_baseChange hX K b
    let r := (PointDivisor.rationalPoint X o ho).baseChange b
    letI : LocallyOfFiniteType PK.obj.hom := inferInstanceAs
      (LocallyOfFiniteType (pullback.snd P.obj.hom b))
    letI : IsSeparated PK.obj.hom := inferInstanceAs (IsSeparated (pullback.snd P.obj.hom b))
    let J := picardIdentityComponent X.hom P R
    let JK := picardIdentityComponent XK.hom PK RK
    let hgK : 0 < coherentGenus K XK :=
      (coherentGenus_arbitraryBaseChange properStructureCohomologyBaseChange X hX K b).symm ▸ hg
    pullbackClass (pullback.fst J.hom b)
        (classOf J.left (thetaLineBundleGroundField hX o ho P R hg)) =
      pullbackClass (jacobianScalarExtensionIso P R K).hom.left
        (classOf JK.left
          (thetaLineBundleGroundField hXK r.sectionMap r.section_comp PK RK hgK)) := by
  let b := Spec.algebraMap k K
  let F := Over.pullback b
  let XK := fieldBaseChange K X
  let PK := LocallyNoetherianOver.baseChange b P
  let RK := baseChangeRepresentableBy X.hom b P R
  let hXK := curveProperties_baseChange hX K b
  let r := (PointDivisor.rationalPoint X o ho).baseChange b
  let : LocallyOfFiniteType PK.obj.hom := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd P.obj.hom b))
  let : IsSeparated PK.obj.hom := inferInstanceAs (IsSeparated (pullback.snd P.obj.hom b))
  let := picardCommGrpObj X.hom P R
  let := picardCommGrpObj XK.hom PK RK
  let J := picardIdentityComponent X.hom P R
  let JK := picardIdentityComponent XK.hom PK RK
  let e : F.obj J ≅ JK := jacobianScalarExtensionIso P R K
  let qP := pullback.fst P.obj.hom b
  let qJ := pullback.fst J.hom b
  let qX := pullback.fst X.hom b
  have hgen : coherentGenus K XK = coherentGenus k X :=
    coherentGenus_arbitraryBaseChange properStructureCohomologyBaseChange X hX K b
  let hgK : 0 < coherentGenus K XK := hgen.symm ▸ hg
  let c := (coherentGenus k X - 1) • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)
  let cK := (coherentGenus K XK - 1) •
    classOf XK.left (PointDivisor.positiveLineBundle XK hXK r.sectionMap r.section_comp)
  have hc : pullbackClass qX c = cK := by
    dsimp only [c, cK]
    rw [← PullbackTensor.Local.pullbackHom_apply, map_nsmul,
      PullbackTensor.Local.pullbackHom_apply]
    rw [hgen]
    exact congrArg ((coherentGenus k X - 1) • ·)
      (PointDivisor.pullbackClass_positiveLineBundle_fieldBaseChange hX o ho K)
  let j := picardIdentityComponentι X.hom P R
  let jK := picardIdentityComponentι XK.hom PK RK
  let t := (GrpObj.mulRight (picardPoint (X := X) P R c)).hom
  let tK := (GrpObj.mulRight (picardPoint (X := XK) PK RK cK)).hom
  let τ : J ⟶ P.obj := j ≫ t
  let τK : JK ⟶ PK.obj := jK ≫ tK
  have ht : F.map t = tK := by
    have h := map_picardTranslation_fieldBaseChange (K := K) P R c
    change F.map t =
      (GrpObj.mulRight (picardPoint (X := XK) PK RK (pullbackClass qX c))).hom at h
    rw [hc] at h
    exact h
  have hj : e.hom ≫ jK = F.map j := jacobianScalarExtensionIso_hom_comp_inclusion P R K
  have hτ : e.hom ≫ τK = F.map τ := by
    change e.hom ≫ jK ≫ tK = F.map (j ≫ t)
    rw [← Category.assoc, hj, ← ht, F.map_comp]
  have hleft : e.hom.left ≫ τK.left ≫ qP = qJ ≫ τ.left := by
    have h := congrArg Over.Hom.left hτ
    rw [Over.comp_left] at h
    rw [← Category.assoc, h]
    exact pullback.lift_fst _ _ _
  let a := classOf P.obj.left (intrinsicThetaLineBundleOnPicard hX P R hg)
  let aK := classOf PK.obj.left (intrinsicThetaLineBundleOnPicard hXK PK RK hgK)
  have ha : pullbackClass qP a = aK :=
    pullbackClass_intrinsicThetaLineBundleOnPicard_fieldBaseChange hX P R K hg
  calc
    _ = pullbackClass qJ (pullbackClass τ.left a) :=
      congrArg (pullbackClass qJ)
        (pullbackClass_intrinsicThetaLineBundleOnPicard_translation hX o ho P R hg).symm
    _ = pullbackClass e.hom.left (pullbackClass τK.left aK) := by
      rw [← ha, ← pullbackClass_comp, ← pullbackClass_comp, ← pullbackClass_comp,
        Category.assoc, hleft]
    _ = _ := congrArg (pullbackClass e.hom.left)
      (pullbackClass_intrinsicThetaLineBundleOnPicard_translation hXK
        r.sectionMap r.section_comp PK RK hgK)

end AlgebraicGeometry.Scheme.OverField.Curve
