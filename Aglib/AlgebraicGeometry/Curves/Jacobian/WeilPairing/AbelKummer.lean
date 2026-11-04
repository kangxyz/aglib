/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.FrameClass
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.Polarization
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Kummer
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.CanonicalPrincipal
public import Aglib.AlgebraicGeometry.EtaleCohomology.Picard.KummerPreimage

/-! # The original Abel pullback of the terminal multiplication family

The positive Abel map followed by the inverse first projection pulls the
actual character pushout to the negative original inverse Kummer class.
The computation uses the original normalized Poincaré class and original
principal isomorphism on the same Jacobian.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open MonoidalCategory MonObj CartesianMonoidalCategory
open Scheme.OverField Scheme.Group Scheme.EtaleCohomology
open Scheme.RelativePicard Scheme.Modules.Invertible
open GroupCohomology.Kummer.Coefficients
open scoped CategoryTheory.MonObj

universe u w w'

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.OverField.Curve

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k}
  (hX : Properties X)
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  (Q : LocallyNoetherianOver (Spec (.of k))) [qLft : LocallyOfFiniteType Q.obj.hom]
  [qSep : IsSeparated Q.obj.hom]
  (RQ : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf (picardIdentityComponent X.hom P R).hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)

set_option hygiene false in
local notation "J" => picardIdentityComponent X.hom P R
set_option hygiene false in
local notation "T₀" => (𝟙_ (FScheme k))
set_option hygiene false in
local notation "J₀" => Grp.X (Functor.obj (Functor.mapGrp (Over.pullback (Over.hom (T₀))))
  (Grp.mk (J)))

/-- The original kernel inclusion supplies the corresponding rational torsion point. -/
def jacobianRationalTorsionOfKernelPoint [IsCommMonObj (J)] (n : ℕ)
    (y : (T₀) ⟶ (MultiplicationKernel.kernelGroup (Grp.mk (J)) n).X) :
    AddSubgroup.torsionBy (Additive ((T₀) ⟶ (J))) (n : ℤ) := by
  let A := Grp.mk (J)
  let q := MultiplicationKernel.multiplicationHom A n
  let yJ := y ≫ (Kernel.inclusion q).hom.hom
  refine ⟨Additive.ofMul yJ, AddSubgroup.torsionBy.nsmul_iff.mpr ?_⟩
  change yJ ^ n = 1
  calc
    _ = yJ ≫ MultiplicationKernel.multiplication A n :=
      (MultiplicationKernel.point_multiplication A n yJ).symm
    _ = y ≫ ((Kernel.inclusion q).hom.hom ≫ q.hom.hom) := by
      rw [MultiplicationKernel.multiplicationHom_hom]
      exact Category.assoc _ _ _
    _ = 1 := by rw [Kernel.inclusion_comp_eq_one, MonObj.comp_one]

omit [IsAlgClosed k] [IsSeparated P.obj.hom] qSep in
/-- On the terminal test the original Picard pullback sees the original
Poincaré line bundle. -/
private theorem picardPoint_terminalFamily_pullback
    [IsProper (J).hom] [GeometricallyIntegral (J).hom]
    (a : X ⟶ (J)) (a₀ : X.left ⟶ (J₀).left)
    (ha₀ : a₀ ≫ pullback.fst (J).hom (T₀).hom = a.left)
    (t₀ : (T₀) ⟶ picardIdentityComponent (J).hom Q RQ) :
    letI := picardCommGrpObj X.hom P R
    picardPoint P R
        (pullbackClass a₀ (classOf (J₀).left (poincarePullback (J) Q RQ t₀).bundle)) =
      (t₀ ≫ picardIdentityComponentPullback P R Q RQ a) ≫ identityComponentι P.obj := by
  let := picardCommGrpObj X.hom P R
  let M : LineBundle (J₀).left := (poincarePullback (J) Q RQ t₀).bundle
  let ρX := pullback.fst X.hom (T₀).hom
  let ρJ := pullback.fst (J).hom (T₀).hom
  let RT := locallyNoetherianRationalPoint k
  have hfst : (ρX ≫ a₀) ≫ ρJ = familyMapOfHom a (T₀) ≫ ρJ :=
    (Category.assoc ρX a₀ ρJ).trans
      ((congrArg (fun f => ρX ≫ f) ha₀).trans (familyMapOfHom_fst a (T₀)).symm)
  have hs : pullback.snd (J).hom (T₀).hom = ρJ ≫ (J).hom := by
    change _ = pullback.fst (J).hom (T₀).hom ≫ (J).hom
    rw [pullback.condition]
    exact (Category.comp_id _).symm
  have hproj : ρX ≫ a₀ = familyMapOfHom a (T₀) := by
    apply pullback.hom_ext hfst
    simp only [hs, ← Category.assoc, hfst]
  let qX : PicardGroup (pullback X.hom (T₀).hom) →+
      (fppfPicardSheaf X.hom).obj.obj (op (T₀)) :=
    ((quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op (T₀))).hom
  let qJ : PicardGroup (J₀).left →+ (fppfPicardSheaf (J).hom).obj.obj (op (T₀)) :=
    ((quotientProjection (J).hom ≫ toFppfPicardSheaf (J).hom).app (op (T₀))).hom
  let fA : (fppfPicardSheaf (J).hom).obj.obj (op (T₀)) →+
      (fppfPicardSheaf X.hom).obj.obj (op (T₀)) :=
    ((fppfPicardPullback a).hom.app (op (T₀))).hom
  let v : PicardGroup (J₀).left := classOf (J₀).left M
  let pD := RQ.homEquiv (ObjectProperty.homMk
    (t₀ ≫ picardIdentityComponentι (J).hom Q RQ) : RT ⟶ Q)
  have hp : R.homEquiv (ObjectProperty.homMk
      ((t₀ ≫ picardIdentityComponentPullback P R Q RQ a) ≫
        identityComponentι P.obj) : RT ⟶ P) = fA pD :=
    homEquiv_comp_picardIdentityComponentPullback P R Q RQ a (T := RT) t₀
  have hf : qX (pullbackClass (familyMapOfHom a (T₀)) v) = fA (qJ v) :=
    fppfPicardPullback_class a (T₀) v
  have hM : qJ v = pD := poincarePullback_fppfClass (J) Q RQ (T := RT) t₀
  have hC : qX (pullbackClass (familyMapOfHom a (T₀)) v) =
      picardPointClass X (pullbackClass a₀ v) := by
    rw [picardPointClass_apply]
    change qX (pullbackClass (familyMapOfHom a (T₀)) v) =
      qX (pullbackClass ρX (pullbackClass a₀ v))
    rw [← pullbackClass_comp, hproj]
  exact (picardPoint_eq_iff P R _ _).2
    (hp.trans ((congrArg fA hM.symm).trans (hf.symm.trans hC)))

variable [hJExt : HasExt.{w'} (AbelianSheaf.{u, u + 1} (J₀).left)]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The original family class at the principal image of the original point. -/
def jacobianTerminalFamilyKummerClass
    (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : k))
    (y : letI := picardCommGrpObj X.hom P R
      letI : GrpObj (J) := grpObjPicardIdentityComponent X.hom P R
      letI : IsCommMonObj (J) := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
      (T₀) ⟶ (MultiplicationKernel.kernelGroup (Grp.mk (J)) n).X) :
    H1Etale.{u, u + 1, w'} (J₀).left (mu (J₀).left n) := by
  letI := picardCommGrpObj X.hom P R
  let Jc := (J)
  letI : GrpObj Jc := grpObjPicardIdentityComponent X.hom P R
  let A : Grp (FScheme k) := Grp.mk Jc
  let RQA : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf A.X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q :=
    RQ
  letI jComm : IsCommMonObj A.X := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
  letI jProj : IsHProjective A.X.hom := isHProjective_identityComponentOver hX P R
  letI jIntegral : GeometricallyIntegral A.X.hom :=
    geometricallyIntegral_identityComponentOver hX P R
  letI jSmooth : Smooth A.X.hom := smooth_identityComponentOver hX P R
  let t : (T₀) ⟶ (dualMultiplicationKernel A Q RQA n).X :=
    y ≫ (principalIsoOnMultiplicationKernel A Q RQA
      (canonicalJacobianPrincipalGroupIso hX P R Q RQ) n).hom.hom.hom
  let jExt : HasExt.{w'} (AbelianSheaf.{u, u + 1}
      ((Over.pullback (T₀).hom).mapGrp.obj A).X.left) := hJExt
  let Y : Scheme.{u} := ((Over.pullback (T₀).hom).mapGrp.obj A).X.left
  let m₀ := @multiplicationFamilyKummerClass.{u, w'} k ‹Field k› A Q qLft RQA
  let m₁ := @m₀ jProj
  let m₂ := @m₁ jIntegral
  let m₃ := @m₂ jSmooth
  let m₄ := @m₃ qSep jComm
  let m₅ := @m₄ n hn (T₀) t
  let ξ : H1Etale.{u, u + 1, w'} Y (mu Y n) := @m₅ jExt hu
  exact ξ

omit [IsAlgClosed k] in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The original terminal class is the original cover class pushed by the positive character. -/
theorem jacobianTerminalFamilyKummerClass_eq_coverPush
    (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : k))
    (y : letI := picardCommGrpObj X.hom P R
      letI : GrpObj (J) := grpObjPicardIdentityComponent X.hom P R
      letI : IsCommMonObj (J) := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
      (T₀) ⟶ (MultiplicationKernel.kernelGroup (Grp.mk (J)) n).X) :
    let ξ : H1Etale.{u, u + 1, w'} (J₀).left (mu (J₀).left n) := by
      letI := picardCommGrpObj X.hom P R
      let Jc := (J)
      letI : GrpObj Jc := grpObjPicardIdentityComponent X.hom P R
      let A : Grp (FScheme k) := Grp.mk Jc
      let RQA : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
          (fppfPicardSheaf A.X.hom).obj ⋙
          CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q :=
        RQ
      letI jComm : IsCommMonObj A.X := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
      letI jProj : IsHProjective A.X.hom := isHProjective_identityComponentOver hX P R
      letI jIntegral : GeometricallyIntegral A.X.hom :=
        geometricallyIntegral_identityComponentOver hX P R
      letI jSmooth : Smooth A.X.hom := smooth_identityComponentOver hX P R
      let t : (T₀) ⟶ (dualMultiplicationKernel A Q RQA n).X :=
        y ≫ (principalIsoOnMultiplicationKernel A Q RQA
          (canonicalJacobianPrincipalGroupIso hX P R Q RQ) n).hom.hom.hom
      let jExt : HasExt.{w'} (AbelianSheaf.{u, u + 1}
          ((Over.pullback (T₀).hom).mapGrp.obj A).X.left) := hJExt
      let Y : Scheme.{u} := ((Over.pullback (T₀).hom).mapGrp.obj A).X.left
      let q := MultiplicationKernel.multiplicationHom A n
      let hq := Multiplication.multiplicationHom_finite_flat_surjective A n hn
      letI : IsFinite q.hom.hom.left := hq.1
      letI : Surjective q.hom.hom.left := hq.2.2
      letI : Etale q.hom.hom.left := by
        simpa only [q, MultiplicationKernel.multiplicationHom_hom,
          MultiplicationKernel.multiplication]
          using Multiplication.multiplication_etale_of_smooth_of_isUnit A n hu
      letI : IsCommMonObj (KernelFramePushout.familyCoefficient q (T₀)).X :=
        KernelFramePushout.familyCoefficient_isCommMonObj q (T₀)
      letI : HasExt.{w'} (AbelianSheaf.{u, u + 1} Y) := jExt
      let χ : representedSheaf (KernelFramePushout.familyCoefficient q (T₀)) ⟶ mu Y n :=
        representedSheafMap (multiplicationFamilyRootCharacter A Q RQA n hn t)
      let c : H1Etale.{u, u + 1, w'} Y
          (representedSheaf (KernelFramePushout.familyCoefficient q (T₀))) :=
        torsorExtClass (KernelFramePushout.familyCoverTorsor q (T₀))
      exact coefficientMap χ c
    jacobianTerminalFamilyKummerClass hX P R Q RQ n hn hu y = ξ := by
  rfl

omit [IsAlgClosed k] in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The terminal-family Kummer class has the original Poincaré Picard image. -/
theorem jacobianTerminalFamilyKummerClass_inclusion
    (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : k))
    (y : letI := picardCommGrpObj X.hom P R
      letI : GrpObj (J) := grpObjPicardIdentityComponent X.hom P R
      letI : IsCommMonObj (J) := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
      (T₀) ⟶ (MultiplicationKernel.kernelGroup (Grp.mk (J)) n).X) :
    letI := picardCommGrpObj X.hom P R
    letI : GrpObj (J) := grpObjPicardIdentityComponent X.hom P R
    letI : IsCommMonObj (J) := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
    letI : IsProper (J).hom := isProper_identityComponentOver hX P R
    letI : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
    let t : (T₀) ⟶ (dualMultiplicationKernel (Grp.mk (J)) Q RQ n).X :=
      y ≫ (principalIsoOnMultiplicationKernel (Grp.mk (J)) Q RQ
        (canonicalJacobianPrincipalGroupIso hX P R Q RQ) n).hom.hom.hom
    let t₀ := t ≫ (dualMultiplicationKernelInclusion (Grp.mk (J)) Q RQ n).hom.hom
    Sheaf.H.map (inclusion (J₀).left n) 1
        (jacobianTerminalFamilyKummerClass hX P R Q RQ n hn hu y) =
      Scheme.EtaleCohomology.Picard.picardCohomologyEquiv (J₀).left
        (classOf (J₀).left (poincarePullback (J) Q RQ t₀).bundle) := by
  let := picardCommGrpObj X.hom P R
  let Jc := (J)
  let : GrpObj Jc := grpObjPicardIdentityComponent X.hom P R
  let A : Grp (FScheme k) := Grp.mk Jc
  let RQA : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf A.X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q :=
    RQ
  let jComm : IsCommMonObj A.X := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
  let jProj : IsHProjective A.X.hom := isHProjective_identityComponentOver hX P R
  let jIntegral : GeometricallyIntegral A.X.hom :=
    geometricallyIntegral_identityComponentOver hX P R
  let jSmooth : Smooth A.X.hom := smooth_identityComponentOver hX P R
  let e := canonicalJacobianPrincipalGroupIso hX P R Q RQ
  let t : (T₀) ⟶ (dualMultiplicationKernel A Q RQA n).X :=
    y ≫ (principalIsoOnMultiplicationKernel A Q RQA e n).hom.hom.hom
  let t₀ := t ≫ (dualMultiplicationKernelInclusion A Q RQA n).hom.hom
  let Y : Scheme.{u} := ((Over.pullback (T₀).hom).mapGrp.obj A).X.left
  let M : LineBundle Y := (poincarePullback A.X Q RQA t₀).bundle
  let jExt : HasExt.{w'} (AbelianSheaf.{u, u + 1} Y) := hJExt
  let ξ : H1Etale.{u, u + 1, w'} Y (mu Y n) :=
    jacobianTerminalFamilyKummerClass hX P R Q RQ n hn hu y
  change Sheaf.H.map (inclusion Y n) 1 ξ =
    Scheme.EtaleCohomology.Picard.picardCohomologyEquiv Y (classOf Y M)
  let m₀ := @multiplicationFamilyKummerClass_inclusion.{u, w'} k ‹Field k› A Q qLft RQA
  let m₁ := @m₀ jProj
  let m₂ := @m₁ jIntegral
  let m₃ := @m₂ jSmooth
  let m₄ := @m₃ qSep jComm
  let m₅ := @m₄ n hn (T₀) t
  exact @m₅ jExt hu

omit [IsAlgClosed k] hJExt in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem principalKernelPoint_abelPicardPoint
    (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
    (n : ℕ)
    (y : letI := picardCommGrpObj X.hom P R
      letI : GrpObj (J) := grpObjPicardIdentityComponent X.hom P R
      letI : IsCommMonObj (J) := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
      (T₀) ⟶ (MultiplicationKernel.kernelGroup (Grp.mk (J)) n).X) :
    letI := picardCommGrpObj X.hom P R
    letI : GrpObj (J) := grpObjPicardIdentityComponent X.hom P R
    letI : IsCommMonObj (J) := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
    letI : IsProper (J).hom := isProper_identityComponentOver hX P R
    letI : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
    let a := jacobianCurveMorphism hX o ho P R
    let iJ : (J).left ⟶ (J₀).left := pullback.lift (𝟙 (J).left) (J).hom (by simp)
    let t : (T₀) ⟶ (dualMultiplicationKernel (Grp.mk (J)) Q RQ n).X :=
      y ≫ (principalIsoOnMultiplicationKernel (Grp.mk (J)) Q RQ
        (canonicalJacobianPrincipalGroupIso hX P R Q RQ) n).hom.hom.hom
    let t₀ := t ≫ (dualMultiplicationKernelInclusion (Grp.mk (J)) Q RQ n).hom.hom
    let M : LineBundle (J₀).left := (poincarePullback (J) Q RQ t₀).bundle
    let z := jacobianRationalTorsionOfKernelPoint P R n y
    picardPoint P R (pullbackClass (a.left ≫ iJ) (classOf (J₀).left M)) =
      (-z).val.toMul ≫ identityComponentι P.obj := by
  let := picardCommGrpObj X.hom P R
  let Jc := (J)
  let : GrpObj Jc := grpObjPicardIdentityComponent X.hom P R
  let A : Grp (FScheme k) := Grp.mk Jc
  let : IsCommMonObj A.X := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
  let : IsProper A.X.hom := isProper_identityComponentOver hX P R
  let : GeometricallyIntegral A.X.hom := geometricallyIntegral_identityComponentOver hX P R
  let e := canonicalJacobianPrincipalGroupIso hX P R Q RQ
  let t : (T₀) ⟶ (dualMultiplicationKernel A Q RQ n).X :=
    y ≫ (principalIsoOnMultiplicationKernel A Q RQ e n).hom.hom.hom
  let t₀ := t ≫ (dualMultiplicationKernelInclusion A Q RQ n).hom.hom
  let Y : Scheme.{u} := ((Over.pullback (T₀).hom).mapGrp.obj A).X.left
  let M : LineBundle Y := (poincarePullback A.X Q RQ t₀).bundle
  let a : X ⟶ Jc := jacobianCurveMorphism hX o ho P R
  let iJ : Jc.left ⟶ Y :=
    pullback.lift (f := Jc.hom) (g := (T₀).hom) (𝟙 Jc.left) Jc.hom (by simp)
  let a₀ : X.left ⟶ Y := a.left ≫ iJ
  let ρJ := pullback.fst Jc.hom (T₀).hom
  have hi : iJ ≫ ρJ = 𝟙 Jc.left := pullback.lift_fst _ _ _
  have ha₀ : a₀ ≫ ρJ = a.left :=
    (Category.assoc a.left iJ ρJ).trans
      ((congrArg (fun f => a.left ≫ f) hi).trans (Category.comp_id _))
  let d := picardIdentityComponentPullback P R Q RQ a
  have hp : picardPoint P R (pullbackClass a₀ (classOf Y M)) =
      (t₀ ≫ d) ≫ identityComponentι P.obj :=
    picardPoint_terminalFamily_pullback P R Q RQ a a₀ ha₀ t₀
  let q := MultiplicationKernel.multiplicationHom A n
  let yJ := y ≫ (Kernel.inclusion q).hom.hom
  have ht : t₀ = yJ ≫ e.hom.hom.hom := by
    let := picardCommGrpObj Jc.hom Q RQ
    let : IsCommMonObj (picardIdentityComponent Jc.hom Q RQ) :=
      inferInstanceAs (IsCommMonObj (identityComponentOver Q.obj))
    have h := MultiplicationKernel.map_inclusion e.hom n
    have h' := congrArg (fun f => f.hom.hom) h
    change (y ≫ (principalIsoOnMultiplicationKernel A Q RQ e n).hom.hom.hom) ≫
        (dualMultiplicationKernelInclusion A Q RQ n).hom.hom =
      (y ≫ (Kernel.inclusion q).hom.hom) ≫ e.hom.hom.hom
    simp only [Category.assoc, principalIsoOnMultiplicationKernel, MultiplicationKernel.mapIso_hom]
    exact congrArg (fun f => y ≫ f) h'
  let s := canonicalJacobianPrincipalIso hX P R Q RQ
  have hs : s.inv = d ≫ ι[Jc] :=
    canonicalJacobianPrincipalIso_inv_originalPullback hX P R Q RQ o ho
  have hLambda : e.hom.hom.hom ≫ d = ι[Jc] := by
    have h : (e.hom.hom.hom ≫ d) ≫ ι[Jc] = 𝟙 Jc := by
      rw [Category.assoc, ← hs]
      exact s.hom_inv_id
    calc
      _ = ((e.hom.hom.hom ≫ d) ≫ ι[Jc]) ≫ ι[Jc] := by
        rw [Category.assoc, GrpObj.inv_comp_inv, Category.comp_id]
      _ = ι[Jc] := by rw [h, Category.id_comp]
  have hsign : t₀ ≫ d = yJ⁻¹ := by
    rw [ht, Category.assoc, hLambda, Hom.inv_def]
  change picardPoint P R (pullbackClass a₀ (classOf Y M)) =
    yJ⁻¹ ≫ identityComponentι P.obj
  exact hp.trans (congrArg (fun f => f ≫ identityComponentι P.obj) hsign)

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)]

omit hJExt in
private theorem abelKummer_eq_neg_of_picardClass {Y : Scheme.{u}}
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y)]
    (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : k))
    (f : X.left ⟶ Y) (hinv : IsUnit (n : Γ(Y, ⊤))) (L : LineBundle Y)
    (ξ : Sheaf.H.{w'} (mu Y n) 1)
    (hξ : Sheaf.H.map (inclusion Y n) 1 ξ =
      Scheme.EtaleCohomology.Picard.picardCohomologyEquiv Y (classOf Y L))
    (z : letI := picardCommGrpObj X.hom P R
      AddSubgroup.torsionBy (Additive ((T₀) ⟶ identityComponentOver P.obj)) (n : ℤ))
    (hP : letI := picardCommGrpObj X.hom P R
      picardPoint P R (pullbackClass f (classOf Y L)) =
        (-z).val.toMul ≫ identityComponentι P.obj) :
    Kummer.rootsCohomologyPullback.{u, w', w} f n hn hinv 1 ξ =
      -(rootsOneJacobianTorsionAddEquiv.{u, w} hX P R n hn hu).symm z := by
  let := picardCommGrpObj X.hom P R
  let c : Sheaf.H.{w} (mu X.left n) 1 :=
    Kummer.rootsCohomologyPullback.{u, w', w} f n hn hinv 1 ξ
  let E := rootsOneJacobianTorsionAddEquiv.{u, w} hX P R n hn hu
  have hC :
      Sheaf.H.map (inclusion X.left n) 1 c =
        Scheme.EtaleCohomology.Picard.picardCohomologyEquiv X.left
          (classOf X.left (pullbackLineBundle f L)) :=
    Scheme.EtaleCohomology.Picard.kummerPreimage_pullback f L n hn hinv ξ hξ
  have hK : Kummer.rootsPicardMap X.left n c = pullbackClass f (classOf Y L) := by
    change (Scheme.EtaleCohomology.Picard.picardCohomologyEquiv X.left).symm
      (Sheaf.H.map (inclusion X.left n) 1 c) = _
    rw [hC, AddEquiv.symm_apply_apply, pullbackClass_classOf]
  have hpointClass := congrFun
    (rootsOneJacobianTorsionAddEquiv_comp_inclusion.{u, w} hX P R n hn hu) c
  have hpoint : (E c).val.toMul = (-z).val.toMul :=
    (cancel_mono (identityComponentι P.obj)).mp
      (hpointClass.trans ((congrArg (picardPoint P R) hK).trans hP))
  have hE : E c = -z := Subtype.ext (Additive.toMul.injective hpoint)
  change c = -E.symm z
  apply E.injective
  rw [map_neg, AddEquiv.apply_symm_apply]
  exact hE

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The positive Abel map pulls the original terminal-family character class
to the negative original inverse Kummer class of the same kernel point. -/
theorem rootsCohomologyPullback_multiplicationFamilyKummerClass_jacobianCurveMorphism
    (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
    (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : k))
    (y : letI := picardCommGrpObj X.hom P R
      letI : GrpObj (J) := grpObjPicardIdentityComponent X.hom P R
      letI : IsCommMonObj (J) := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
      (T₀) ⟶ (MultiplicationKernel.kernelGroup (Grp.mk (J)) n).X) :
    letI := picardCommGrpObj X.hom P R
    letI : GrpObj (J) := grpObjPicardIdentityComponent X.hom P R
    letI : IsCommMonObj (J) := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
    let a := jacobianCurveMorphism hX o ho P R
    let iJ : (J).left ⟶ (J₀).left := pullback.lift (𝟙 (J).left) (J).hom (by simp)
    let a₀ : X.left ⟶ (J₀).left := a.left ≫ iJ
    let hinv : IsUnit (n : Γ((J₀).left, ⊤)) := by
      simpa only [map_natCast] using hu.map (Scheme.constants (J₀))
    Kummer.rootsCohomologyPullback.{u, w', w} a₀ n hn hinv 1
        (jacobianTerminalFamilyKummerClass hX P R Q RQ n hn hu y) =
      -(rootsOneJacobianTorsionAddEquiv.{u, w} hX P R n hn hu).symm
        (jacobianRationalTorsionOfKernelPoint P R n y) := by
  let := picardCommGrpObj X.hom P R
  let Jc := (J)
  let : GrpObj Jc := grpObjPicardIdentityComponent X.hom P R
  let A : Grp (FScheme k) := Grp.mk Jc
  let : IsCommMonObj A.X := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
  let : IsProper A.X.hom := isProper_identityComponentOver hX P R
  let : GeometricallyIntegral A.X.hom := geometricallyIntegral_identityComponentOver hX P R
  let Y : Scheme.{u} := (J₀).left
  let : HasExt.{w'} (AbelianSheaf.{u, u + 1} Y) := hJExt
  let t : (T₀) ⟶ (dualMultiplicationKernel A Q RQ n).X :=
    y ≫ (principalIsoOnMultiplicationKernel A Q RQ
      (canonicalJacobianPrincipalGroupIso hX P R Q RQ) n).hom.hom.hom
  let t₀ := t ≫ (dualMultiplicationKernelInclusion A Q RQ n).hom.hom
  let M : LineBundle Y := (poincarePullback A.X Q RQ t₀).bundle
  let ξ : Sheaf.H.{w'} (mu Y n) 1 :=
    jacobianTerminalFamilyKummerClass hX P R Q RQ n hn hu y
  let a : X ⟶ Jc := jacobianCurveMorphism hX o ho P R
  let iJ : Jc.left ⟶ Y :=
    pullback.lift (f := Jc.hom) (g := (T₀).hom) (𝟙 Jc.left) Jc.hom (by simp)
  let a₀ : X.left ⟶ Y := a.left ≫ iJ
  let hinv : IsUnit (n : Γ(Y, ⊤)) := by
    simpa only [map_natCast] using hu.map (Scheme.constants (J₀))
  let z := jacobianRationalTorsionOfKernelPoint P R n y
  have hξ : Sheaf.H.map (inclusion Y n) 1 ξ =
      Scheme.EtaleCohomology.Picard.picardCohomologyEquiv Y (classOf Y M) :=
    jacobianTerminalFamilyKummerClass_inclusion hX P R Q RQ n hn hu y
  have hp : picardPoint P R (pullbackClass a₀ (classOf Y M)) =
      (-z).val.toMul ≫ identityComponentι P.obj :=
    principalKernelPoint_abelPicardPoint hX P R Q RQ o ho n y
  change Kummer.rootsCohomologyPullback.{u, w', w} a₀ n hn hinv 1 ξ =
    -(rootsOneJacobianTorsionAddEquiv.{u, w} hX P R n hn hu).symm z
  exact abelKummer_eq_neg_of_picardClass hX P R n hn hu a₀ hinv M ξ hξ z hp

end AlgebraicGeometry.Scheme.OverField.Curve
