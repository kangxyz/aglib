/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Ample
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.SourcePullback

/-! # Positivity from the original Abel pullback

The complete geometric argument uses the original theta bundle and arbitrary
representations on the supplied Picard parameter. Source pullback transports
the induced dual components; it does not identify their group structures.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open Opposite AlgebraicGeometry Scheme Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Group
open Scheme.Modules.Invertible.PullbackTensor.Local
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original negative Abel pullback equation identifies the morphism
of the specific theta class pulled back along the given source comparison. -/
theorem geometricTheta_of_originalAbelPullback
    {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Properties X)
    (u : 𝟙_ (FScheme k) ⟶ X)
    (P : LocallyNoetherianOver (Spec (.of k)))
    (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf X.hom).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
    [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]
    (A : FScheme k) [GrpObj A] [IsProper A.hom] [GeometricallyIntegral A.hom]
    (Q : LocallyNoetherianOver (Spec (.of k)))
    [LocallyOfFiniteType Q.obj.hom]
    (RQA : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf A.hom).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)
    (RQB : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf (picardIdentityComponent X.hom P R).hom).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)
    (e : A ≅ picardIdentityComponent X.hom P R)
    (he : letI := picardCommGrpObj X.hom P R; IsMonHom e.hom)
    (f : X ⟶ A) (hf : f ≫ e.hom = jacobianCurveMorphism hX u.left u.w P R)
    (p : A ⟶ picardIdentityComponent A.hom Q RQA)
    [Mono (picardIdentityComponentPullback (X := X) (Y := A) P R Q RQA f)]
    (hp : letI := picardCommGrpObj X.hom P R
      p ≫ picardIdentityComponentPullback (X := X) (Y := A) P R Q RQA f =
        e.hom ≫ ι[picardIdentityComponent X.hom P R])
    (hg : 0 < coherentGenus k X) :
    p = lineBundleClassMorphismIdentityComponent A Q RQA
      (classOf A.left (pullbackLineBundle e.hom.left
        (thetaLineBundle hX u.left u.w P R hg))) := by
  let := picardCommGrpObj X.hom P R
  let B := picardIdentityComponent X.hom P R
  let : IsMonHom e.hom := he
  let : IsHProjective B.hom := isHProjective_identityComponentOver hX P R
  let : Smooth B.hom := smooth_identityComponentOver hX P R
  let : GeometricallyIntegral B.hom := geometricallyIntegral_identityComponentOver hX P R
  let θ := thetaLineBundle hX u.left u.w P R hg
  let φ := lineBundleClassMorphismIdentityComponent B Q RQB (classOf B.left θ)
  let r := picardIdentityComponentPullback (X := X) (Y := A) P R Q RQA f
  let s := picardIdentityComponentPullback (X := A) (Y := B) Q RQA Q RQB e.hom
  have hPB := picardIdentityComponentPullback_comp (X := X) (Y := A) (Z := B)
    P R Q RQA Q RQB f e.hom
  rw [hf] at hPB
  have hPBpost := congrArg (e.hom ≫ φ ≫ ·) hPB
  have hθ := thetaAutoduality hX u.left u.w P R Q RQB hg
  have hpositive : p = e.hom ≫ φ ≫ s := by
    apply (cancel_mono r).mp
    calc
      _ = e.hom ≫ ι[B] := hp
      _ = e.hom ≫ (φ ≫ picardIdentityComponentPullback (X := X) (Y := B)
          P R Q RQB (jacobianCurveMorphism hX u.left u.w P R)) :=
        congrArg (e.hom ≫ ·) hθ.symm
      _ = _ := by simpa only [Category.assoc] using hPBpost
  have hφ := lineBundleClassMorphismIdentityComponent_sourceHom A B Q RQA Q RQB
    e.hom (classOf B.left θ)
  have H := hpositive.trans hφ.symm
  rw [pullbackClass_classOf] at H
  exact H

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A morphism whose original Abel pullback is minus the native source
comparison is induced by the ample pullback of the original theta bundle. -/
theorem geometricPositive_of_originalAbelPullback
    {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Properties X)
    (u : 𝟙_ (FScheme k) ⟶ X)
    (P : LocallyNoetherianOver (Spec (.of k)))
    (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf X.hom).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
    [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]
    (A : FScheme k) [GrpObj A] [IsProper A.hom] [GeometricallyIntegral A.hom]
    (Q : LocallyNoetherianOver (Spec (.of k)))
    [LocallyOfFiniteType Q.obj.hom] [IsSeparated Q.obj.hom]
    (RQA : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf A.hom).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)
    (RQB : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf (picardIdentityComponent X.hom P R).hom).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)
    (e : A ≅ picardIdentityComponent X.hom P R)
    (he : letI := picardCommGrpObj X.hom P R; IsMonHom e.hom)
    (f : X ⟶ A) (hf : f ≫ e.hom = jacobianCurveMorphism hX u.left u.w P R)
    (p : A ⟶ picardIdentityComponent A.hom Q RQA)
    [Mono (picardIdentityComponentPullback (X := X) (Y := A) P R Q RQA f)]
    (hp : letI := picardCommGrpObj X.hom P R
      p ≫ picardIdentityComponentPullback (X := X) (Y := A) P R Q RQA f =
        e.hom ≫ ι[picardIdentityComponent X.hom P R])
    (hg : 0 < coherentGenus k X) :
    ∃ L : LineBundle A.left, L.IsAmple ∧
      p = lineBundleClassMorphismIdentityComponent A Q RQA (classOf A.left L) := by
  let := picardCommGrpObj X.hom P R
  let θ := thetaLineBundle hX u.left u.w P R hg
  refine ⟨pullbackLineBundle e.hom.left θ,
    (thetaLineBundle_isAmple hX u.left u.w P R Q RQB hg).pullback_of_isAffineHom e.hom.left, ?_⟩
  exact geometricTheta_of_originalAbelPullback hX u P R A Q RQA RQB e he f hf p hp hg

end AlgebraicGeometry.Scheme.OverField.Curve
