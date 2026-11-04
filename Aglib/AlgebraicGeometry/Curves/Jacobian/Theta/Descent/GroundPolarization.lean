/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Descent.BasedClassBaseChange
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.CanonicalPrincipal
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.BaseChange

/-! The original ground-field theta bundle induces the original principal map. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Scheme.Cohomology Scheme.RelativePicard Scheme.Modules.Invertible
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
  (Q : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType Q.obj.hom]
  [IsSeparated Q.obj.hom]
  (RQ : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf (picardIdentityComponent X.hom P R).hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)

/-- The line-bundle morphism of the original ground-field theta is exactly
the already constructed canonical principal morphism on the same Jacobian.
The comparison uses the actual lifted origin and the same Picard components. -/
theorem lineBundleClassMorphismIdentityComponent_thetaLineBundleGroundField
    (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    let J := picardIdentityComponent X.hom P R
    letI : IsProper J.hom := isProper_identityComponentOver hX P R
    letI : GeometricallyIntegral J.hom := geometricallyIntegral_identityComponentOver hX P R
    lineBundleClassMorphismIdentityComponent J Q RQ
        (classOf J.left (thetaLineBundleGroundField hX o ho P R hg)) =
      (canonicalJacobianPrincipalIso hX P R Q RQ).hom := by
  let := picardCommGrpObj X.hom P R
  let J := picardIdentityComponent X.hom P R
  let : IsProper J.hom := isProper_identityComponentOver hX P R
  let : GeometricallyIntegral J.hom := geometricallyIntegral_identityComponentOver hX P R
  let K := AlgebraicClosure k
  let b := Spec.algebraMap k K
  let F := Over.pullback b
  let A := fieldBaseChange K J
  let : GrpObj A := Functor.grpObjObj (F := F) (G := J)
  let : IsProper A.hom := inferInstanceAs (IsProper (pullback.snd J.hom b))
  let : GeometricallyIntegral A.hom := inferInstanceAs
    (GeometricallyIntegral (pullback.snd J.hom b))
  let QK := LocallyNoetherianOver.baseChange b Q
  let RQA := baseChangeRepresentableBy J.hom b Q RQ
  let : LocallyOfFiniteType QK.obj.hom := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd Q.obj.hom b))
  let : IsSeparated QK.obj.hom := inferInstanceAs (IsSeparated (pullback.snd Q.obj.hom b))
  let XK := fieldBaseChange K X
  let hXK := curveProperties_baseChange hX K b
  let PK := LocallyNoetherianOver.baseChange b P
  let RK := baseChangeRepresentableBy X.hom b P R
  let : LocallyOfFiniteType PK.obj.hom := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd P.obj.hom b))
  let : IsSeparated PK.obj.hom := inferInstanceAs (IsSeparated (pullback.snd P.obj.hom b))
  let e := jacobianScalarExtensionIso P R K
  let r := (PointDivisor.rationalPoint X o ho).baseChange b
  let u : 𝟙_ (FScheme K) ⟶ XK := Over.homMk r.sectionMap r.section_comp
  let hgK : 0 < coherentGenus K XK :=
    (coherentGenus_arbitraryBaseChange properStructureCohomologyBaseChange X hX K b).symm ▸ hg
  let a := classOf J.left (thetaLineBundleGroundField hX o ho P R hg)
  let aK := pullbackClass (pullback.fst J.hom b) a
  let θK := thetaLineBundle hXK u.left u.w PK RK hgK
  have hθ : aK = classOf A.left (pullbackLineBundle e.hom.left θK) := by
    let JK := picardIdentityComponent XK.hom PK RK
    let M := thetaLineBundleGroundField hXK u.left u.w PK RK hgK
    have h : aK = pullbackClass e.hom.left (classOf JK.left M) :=
      pullbackClass_thetaLineBundleGroundField_fieldBaseChange hX o ho P R K hg
    have hM : M = θK := thetaLineBundleGroundField_eq hXK u.left u.w PK RK hgK
    exact h.trans (congrArg (fun N => pullbackClass e.hom.left (classOf JK.left N)) hM)
  let D := picardIdentityComponent J.hom Q RQ
  let DK := picardIdentityComponent A.hom QK RQA
  let eD : fieldBaseChange K D ≅ DK := Over.isoMk
    (picardIdentityComponentBaseChangeIso J.hom Q RQ K)
    (picardIdentityComponentBaseChangeIso_hom_comp J.hom Q RQ K)
  let lambda := (canonicalJacobianPrincipalIso hX P R Q RQ).hom
  let φ := lineBundleClassMorphismIdentityComponent J Q RQ a
  let φK := lineBundleClassMorphismIdentityComponent A QK RQA aK
  have hLambda : F.map lambda ≫ eD.hom = φK := by
    have h := canonicalThetaPrincipalIso_geometricTheta hX P R Q RQ
      (jacobianStructureH1Le hX P R) K u hg
    change F.map lambda ≫ eD.hom =
      lineBundleClassMorphismIdentityComponent A QK RQA
        (classOf A.left (pullbackLineBundle e.hom.left θK)) at h
    exact h.trans (congrArg (lineBundleClassMorphismIdentityComponent A QK RQA) hθ.symm)
  let j := picardIdentityComponentι J.hom Q RQ
  let jK := picardIdentityComponentι A.hom QK RQA
  have heD : eD.hom ≫ jK = F.map j := by
    apply Over.OverMorphism.ext
    exact picardIdentityComponentBaseChangeIso_hom_ι Q RQ K
  have hφ : F.map φ ≫ eD.hom = φK := by
    apply (cancel_mono jK).mp
    calc
      _ = F.map (φ ≫ j) := by rw [Category.assoc, heD, F.map_comp]
      _ = F.map (lineBundleClassMorphism J Q RQ a) :=
        congrArg F.map (lineBundleClassMorphismIdentityComponent_ι J Q RQ a)
      _ = _ := (lineBundleClassMorphismIdentityComponent_baseChange_ι b J Q RQ a).symm
  let : Surjective b := ⟨Function.surjective_to_subsingleton b⟩
  let : Flat b := inferInstanceAs (Flat (Spec.algebraMap k K))
  let : ∀ (Z : Scheme.{u}) (g : Z ⟶ Base k), Epi (pullback.fst g b) :=
    fun _ g => Flat.epi_of_flat_of_surjective (pullback.fst g b)
  let : F.Faithful := Over.faithful_pullback b
  exact F.map_injective ((cancel_mono eD.hom).mp (hφ.trans hLambda.symm))

end AlgebraicGeometry.Scheme.OverField.Curve
