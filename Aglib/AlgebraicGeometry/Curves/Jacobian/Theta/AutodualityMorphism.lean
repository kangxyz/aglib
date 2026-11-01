/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.AutodualityClass
public import Aglib.AlgebraicGeometry.Curves.Jacobian.ProjectivityField
public import Aglib.AlgebraicGeometry.Picard.Scheme.Pullback
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.FamilyFormula
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.Translation

/-!
# The original theta autoduality morphism

The whole relative class equality on the original dense open gives an
equality of the actual represented morphisms. Extend it to the original
reduced Jacobian using separatedness of the same Picard representative.
The original unit equation cancels the constant coefficient. Inversion
invariance of the theta line-bundle morphism supplies Milne's minus sign.
No geometric property of the dual Picard component is assumed.
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

omit [IsAlgClosed k] [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem homEquiv_constant_picardPoint
    (T : LocallyNoetherianOver (Spec (.of k))) (a : PicardGroup X.left) :
    R.homEquiv (ObjectProperty.homMk
      (toUnit T.obj ≫ picardPoint P R a) : T ⟶ P) =
      (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T.obj)
        (pullbackClass (pullback.fst X.hom T.obj.hom) a) := by
  change R.homEquiv ((ObjectProperty.homMk (toUnit T.obj) :
    T ⟶ locallyNoetherianRationalPoint k) ≫
      (ObjectProperty.homMk (picardPoint P R a) : locallyNoetherianRationalPoint k ⟶ P)) = _
  rw [R.homEquiv_comp, homEquiv_picardPoint]
  have h := (NatTrans.naturality_apply (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom)
    (toUnit T.obj).op (pullbackClass (pullback.fst X.hom (𝟙 (Spec (.of k)))) a)).symm
  change (fppfPicardSheaf X.hom).obj.map (toUnit T.obj).op (picardPointClass X a) = _
  have hc : (familyPicardFunctor X.hom).map (toUnit T.obj).op
      (pullbackClass (pullback.fst X.hom (𝟙 (Spec (.of k)))) a) =
        pullbackClass (pullback.fst X.hom T.obj.hom) a := by
    change pullbackClass ((familyScheme X.hom).map (toUnit T.obj))
      (pullbackClass (pullback.fst X.hom (𝟙 (Spec (.of k)))) a) = _
    rw [← pullbackClass_comp]
    exact congrArg (fun v => pullbackClass v a) (familyScheme_map_fst X.hom (toUnit T.obj))
  exact (congrArg (fun z => (fppfPicardSheaf X.hom).obj.map (toUnit T.obj).op z)
    (picardPointClass_apply X a)).trans (h.trans
      (congrArg (fun z => (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app
        (op T.obj) z) hc))

local notation "J" => picardIdentityComponent X.hom P R

variable (Q : LocallyNoetherianOver (Spec (.of k)))
  (RQ : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf (picardIdentityComponent X.hom P R).hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)
  [LocallyOfFiniteType Q.obj.hom] [IsSeparated Q.obj.hom]

omit [LocallyOfFiniteType Q.obj.hom] [IsSeparated Q.obj.hom] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On the actual retained open, the original pulled-back line-bundle
morphism is the original degree-g classifying map divided by one fixed
curve Picard point. This is equality of morphisms, not of field values. -/
theorem thetaAutoduality_restriction (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    letI : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
    letI : Smooth (J).hom := smooth_identityComponentOver hX P R
    letI : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
    let V := thetaParameterOver hX o ho P R
    let a := classOf (J).left (thetaLineBundle hX o ho P R hg)
    let B := pullbackClass (jacobianCurveMorphism hX o ho P R).left
      (pullbackClass ι[J].left a)
    thetaParameterι hX o ho P R ≫ ι[J] ≫
      lineBundleClassMorphism J Q RQ (pullbackClass ι[J].left a) ≫
        picardPullback P R Q RQ (jacobianCurveMorphism hX o ho P R) =
      (thetaParameterι hX o ho P R ≫ identityComponentι P.obj ≫
        (GrpObj.mulRight (picardPoint P R (coherentGenus k X • classOf X.left
          (PointDivisor.positiveLineBundle X hX o ho)))).hom) /
        (toUnit V ≫ picardPoint P R B) := by
  let := picardCommGrpObj X.hom P R
  let : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
  let : Smooth (J).hom := smooth_identityComponentOver hX P R
  let : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
  let V := thetaParameterOver hX o ho P R
  let T : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨V, thetaParameter_isLocallyNoetherian hX o ho P R⟩
  let a := classOf (J).left (thetaLineBundle hX o ho P R hg)
  let f := jacobianCurveMorphism hX o ho P R
  let t := thetaParameterι hX o ho P R ≫ ι[J]
  let B := pullbackClass f.left (pullbackClass ι[J].left a)
  let φ := lineBundleClassMorphism J Q RQ (pullbackClass ι[J].left a)
  let pb := picardPullback P R Q RQ f
  let d := thetaParameterι hX o ho P R ≫ identityComponentι P.obj ≫
    (GrpObj.mulRight (picardPoint P R (coherentGenus k X • classOf X.left
      (PointDivisor.positiveLineBundle X hX o ho)))).hom
  let c := toUnit V ≫ picardPoint P R B
  have hleft : R.homEquiv (ObjectProperty.homMk ((t ≫ φ) ≫ pb) : T ⟶ P) =
      (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op V)
        (pullbackClass (familyMapOfHom f V)
          (translationFamilyClass J t (pullbackClass ι[J].left a))) := by
    rw [homEquiv_comp_picardPullback, fppf_homEquiv_comp_lineBundleClassMorphism]
    exact (fppfPicardPullback_class f V _).symm
  have hright : R.homEquiv (ObjectProperty.homMk (d / c) : T ⟶ P) =
      Sub.sub (α := (fppfPicardSheaf X.hom).obj.obj (op V))
        (R.homEquiv (ObjectProperty.homMk d : T ⟶ P))
        (R.homEquiv (ObjectProperty.homMk c : T ⟶ P)) := by
    exact (picardHomAddEquiv X.hom P R T).map_sub (Additive.ofMul d) (Additive.ofMul c)
  have heq : (ObjectProperty.homMk ((t ≫ φ) ≫ pb) : T ⟶ P) =
      ObjectProperty.homMk (d / c) := by
    apply R.homEquiv.injective
    exact hleft.trans ((theta_sourcePullback_translationFppfClass hX o ho P R hg).trans
      ((congrArg (Sub.sub (α := (fppfPicardSheaf X.hom).obj.obj (op V))
        (R.homEquiv (ObjectProperty.homMk d : T ⟶ P)))
        (homEquiv_constant_picardPoint P R T B).symm).trans hright.symm))
  simpa only [ObjectProperty.homMk_hom, t, φ, pb, d, c, V, T, a, B, f, Category.assoc] using
    congrArg (fun q : T ⟶ P => q.hom) heq

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem thetaParameterι_dominant (hg : 0 < coherentGenus k X) :
    IsDominant (thetaParameterι hX o ho P R).left := by
  let := picardCommGrpObj X.hom P R
  constructor
  change Dense (Set.range (rankOneNonRepeatedOpen hX o ho P R).ι)
  rw [Scheme.Opens.range_ι]
  exact rankOneNonRepeatedOpen_dense hX o ho P R hg

omit [IsSeparated Q.obj.hom] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual theta morphism followed by original Abel pullback is
minus the original Jacobian inclusion into P. The equality holds on the
entire scheme and needs no properness or smoothness of the dual component. -/
theorem thetaAutoduality_fullPicard (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    letI : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
    letI : Smooth (J).hom := smooth_identityComponentOver hX P R
    letI : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
    lineBundleClassMorphism J Q RQ (classOf (J).left (thetaLineBundle hX o ho P R hg)) ≫
      picardPullback P R Q RQ (jacobianCurveMorphism hX o ho P R) =
        ι[J] ≫ identityComponentι P.obj := by
  let := picardCommGrpObj X.hom P R
  let : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
  let : Smooth (J).hom := smooth_identityComponentOver hX P R
  let : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
  let := picardCommGrpObj (J).hom Q RQ
  let a := classOf (J).left (thetaLineBundle hX o ho P R hg)
  let f := jacobianCurveMorphism hX o ho P R
  let B := pullbackClass f.left (pullbackClass ι[J].left a)
  let φ := lineBundleClassMorphism J Q RQ (pullbackClass ι[J].left a)
  let pb := picardPullback P R Q RQ f
  let g0 := picardPoint P R (coherentGenus k X • classOf X.left
    (PointDivisor.positiveLineBundle X hX o ho))
  let b0 := picardPoint P R B
  let γ : J ⟶ P.obj := (identityComponentι P.obj ≫ (GrpObj.mulRight g0).hom) /
    (toUnit J ≫ b0)
  let i := thetaParameterι hX o ho P R
  have hi : i ≫ (ι[J] ≫ φ ≫ pb) = i ≫ γ := by
    simpa only [γ, GrpObj.comp_div, Category.assoc, comp_toUnit_assoc] using
      thetaAutoduality_restriction hX o ho P R Q RQ hg
  have : IsIntegral (J).left := GeometricallyIntegral.isIntegral_of_subsingleton (J).hom
  have : IsDominant i.left := thetaParameterι_dominant hX o ho P R hg
  have H : ι[J] ≫ φ ≫ pb = γ := by
    apply Over.OverMorphism.ext
    exact ext_of_isDominant_of_isSeparated P.obj.hom (by rw [Over.w, Over.w]) i.left
      (congrArg Over.Hom.left hi)
  have : IsMonHom pb := isMonHom_picardPullback P R Q RQ f
  have hu : η[J] ≫ (ι[J] ≫ φ ≫ pb) = η[P.obj] := by
    rw [← Category.assoc, GrpObj.one_inv, ← Category.assoc,
      lineBundleClassMorphism_pointed]
    exact IsMonHom.one_hom pb
  have hγ : γ = (identityComponentι P.obj * (toUnit J ≫ g0)) / (toUnit J ≫ b0) := by
    dsimp only [γ]
    congr 1
    change identityComponentι P.obj ≫ ((𝟙 P.obj) * (toUnit P.obj ≫ g0)) = _
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]
  have hiunit : η[J] ≫ identityComponentι P.obj = η[P.obj] :=
    IsMonHom.one_hom (identityComponentι P.obj)
  have huγ : η[J] ≫ γ = g0 / b0 := by
    rw [hγ, GrpObj.comp_div, MonObj.comp_mul, hiunit]
    simp only [comp_toUnit_assoc, toUnit_unit, Category.id_comp,
      MonObj.one_eq_one, one_mul]
  have hc : g0 / b0 = η[P.obj] :=
    huγ.symm.trans ((congrArg (fun v : J ⟶ P.obj => η[J] ≫ v) H.symm).trans hu)
  have hgb : g0 = b0 := div_eq_one.mp (by simpa only [MonObj.one_eq_one] using hc)
  have H' : ι[J] ≫ φ ≫ pb = identityComponentι P.obj := by
    rw [H, hγ, hgb, mul_div_cancel_right]
  have H'' : ι[J] ≫ lineBundleClassMorphism J Q RQ a ≫ pb =
      identityComponentι P.obj := by
    simpa only [φ, lineBundleClassMorphism_pullback_inv] using H'
  have h := congrArg (fun v : J ⟶ P.obj => ι[J] ≫ v) H''
  rw [← Category.assoc, GrpObj.inv_comp_inv, Category.id_comp] at h
  exact h

omit [IsSeparated Q.obj.hom] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Milne's sign on the original Picard identity components:
the original Abel pullback after phiTheta is minus identity. -/
theorem thetaAutoduality (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    letI : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
    letI : Smooth (J).hom := smooth_identityComponentOver hX P R
    letI : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
    letI := picardCommGrpObj (J).hom Q RQ
    lineBundleClassMorphismIdentityComponent J Q RQ
        (classOf (J).left (thetaLineBundle hX o ho P R hg)) ≫
      picardIdentityComponentPullback P R Q RQ (jacobianCurveMorphism hX o ho P R) = ι[J] := by
  let := picardCommGrpObj X.hom P R
  let : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
  let : Smooth (J).hom := smooth_identityComponentOver hX P R
  let : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
  let := picardCommGrpObj (J).hom Q RQ
  apply (cancel_mono (identityComponentι P.obj)).mp
  rw [Category.assoc, picardIdentityComponentPullback_ι, ← Category.assoc,
    lineBundleClassMorphismIdentityComponent_ι]
  exact thetaAutoduality_fullPicard hX o ho P R Q RQ hg

omit [IsSeparated Q.obj.hom] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Negative Abel pullback is an actual scheme left inverse to the
original theta morphism. -/
theorem thetaAutoduality_leftInverse (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    letI : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
    letI : Smooth (J).hom := smooth_identityComponentOver hX P R
    letI : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
    letI := picardCommGrpObj (J).hom Q RQ
    lineBundleClassMorphismIdentityComponent J Q RQ
        (classOf (J).left (thetaLineBundle hX o ho P R hg)) ≫
      (picardIdentityComponentPullback P R Q RQ (jacobianCurveMorphism hX o ho P R) ≫ ι[J]) =
        𝟙 J := by
  let := picardCommGrpObj X.hom P R
  let : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
  let : Smooth (J).hom := smooth_identityComponentOver hX P R
  let : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
  let := picardCommGrpObj (J).hom Q RQ
  rw [← Category.assoc, thetaAutoduality, GrpObj.inv_comp_inv]

omit [IsSeparated Q.obj.hom] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The left inverse makes the original theta morphism monic as a
scheme morphism; this detects its full scheme kernel. -/
theorem mono_thetaLineBundleMorphism (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    letI : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
    letI : Smooth (J).hom := smooth_identityComponentOver hX P R
    letI : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
    letI := picardCommGrpObj (J).hom Q RQ
    Mono (lineBundleClassMorphismIdentityComponent J Q RQ
      (classOf (J).left (thetaLineBundle hX o ho P R hg))).left := by
  let := picardCommGrpObj X.hom P R
  let : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
  let : Smooth (J).hom := smooth_identityComponentOver hX P R
  let : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
  let := picardCommGrpObj (J).hom Q RQ
  let φ := lineBundleClassMorphismIdentityComponent J Q RQ
    (classOf (J).left (thetaLineBundle hX o ho P R hg))
  let r := picardIdentityComponentPullback P R Q RQ (jacobianCurveMorphism hX o ho P R) ≫ ι[J]
  have h : φ.left ≫ r.left = 𝟙 (J).left :=
    congrArg Over.Hom.left (thetaAutoduality_leftInverse hX o ho P R Q RQ hg)
  have : Mono (φ.left ≫ r.left) := by rw [h]; infer_instance
  exact mono_of_mono φ.left r.left

end AlgebraicGeometry.Scheme.OverField.Curve
