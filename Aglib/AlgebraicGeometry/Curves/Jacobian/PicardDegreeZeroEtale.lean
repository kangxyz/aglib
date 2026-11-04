/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.MarkedCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RelativePicardSheaf.RepresentedComparison
public import Aglib.AlgebraicGeometry.Curves.Jacobian.FiniteFlat
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedMultiplicationBaseChange
public import Aglib.AlgebraicGeometry.Picard.BaseChangeGroupLaw

/-! The original represented Jacobian in the base-changed Picard sheaf. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

@[expose] public noncomputable section

namespace CategoryTheory.Grp

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]

/-- The comparison of equal group laws acts by the identity on the original object. -/
theorem eqToIso_mk_law_hom {X : C} {a b : GrpObj X} (h : a = b) :
    (eqToIso (congrArg (fun law : GrpObj X => @Grp.mk C _ _ X law) h)).hom.hom.hom =
      𝟙 X := by
  subst b
  rfl

end CategoryTheory.Grp

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] Over.cartesianMonoidalCategory

/-- An original represented map followed by a sheaf map evaluates at the composed section. -/
theorem representedSheafMap_then_apply {S : Scheme.{u}} {G H : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X] (m : G ⟶ H)
    {P : AbelianSheaf.{u, u + 1} S} (r : representedSheaf H ⟶ P)
    (U : S.Etale) (x : (Scheme.Etale.forget S).obj U ⟶ G.X) :
    (representedSheafMap m ≫ r).hom.app (op U) (ULift.up (Additive.ofMul x)) =
      r.hom.app (op U) (ULift.up (Additive.ofMul (x ≫ m.hom.hom))) := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Scheme.RelativePicard Scheme.Group Scheme.EtaleCohomology Scheme.Group.BaseChange
open Scheme.EtaleCohomology.MarkedCoefficients

universe u

attribute [local instance] Over.cartesianMonoidalCategory groupSchemeBaseChange_isCommMonObj

variable {k : Type u} [Field k] {X : FScheme k}
  (hX : Properties X)
  (P : LocallyNoetherianOver (Base k)) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Base k)).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  {S : Scheme.{u}} (f : S ⟶ Base k)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original identity component maps to the original represented Picard group. -/
abbrev picardIdentityComponentGroupInclusion :=
  let := picardCommGrpObj X.hom P R
  let J := Grp.mk (picardIdentityComponent X.hom P R)
  let G := Grp.mk P.obj
  let := isMonHom_picardIdentityComponentι X.hom P R
  Grp.homMk (A := J) (B := G) (picardIdentityComponentι X.hom P R)

variable [IsLocallyNoetherian S]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original base change and the original base-changed Picard representation
give the same group structure on the same scheme. -/
def picardRepresenterGroupBaseChangeIso :
    letI := picardCommGrpObj X.hom P R
    let Q := LocallyNoetherianOver.baseChange f P
    let hQ := baseChangeRepresentableBy X.hom f P R
    let QLaw := picardCommGrpObj (pullback.snd X.hom f) Q hQ
    (groupSchemeBaseChange f).functor.obj (Grp.mk P.obj) ≅
      @Grp.mk _ _ _ Q.obj QLaw.toGrpObj := by
  dsimp only
  let := picardCommGrpObj X.hom P R
  let Q := LocallyNoetherianOver.baseChange f P
  let h := picardCommGrpObj_baseChange_toGrpObj X.hom f P R
  exact eqToIso ((congrArg (fun law : GrpObj Q.obj => @Grp.mk _ _ _ Q.obj law) h).symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original group-law comparison is the identity on the original base-changed scheme. -/
theorem picardRepresenterGroupBaseChangeIso_hom_identity :
    letI := picardCommGrpObj X.hom P R
    (picardRepresenterGroupBaseChangeIso P R f).hom.hom.hom =
      𝟙 (LocallyNoetherianOver.baseChange f P).obj := by
  dsimp only
  let := picardCommGrpObj X.hom P R
  let Q := LocallyNoetherianOver.baseChange f P
  let h := picardCommGrpObj_baseChange_toGrpObj X.hom f P R
  let e := congrArg (fun law : GrpObj Q.obj => @Grp.mk _ _ _ Q.obj law) h
  change (eqToIso e.symm).hom.hom.hom = 𝟙 Q.obj
  exact Grp.eqToIso_mk_law_hom h.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original Jacobian group map into the base-changed Picard representer. -/
abbrev picardDegreeZeroEtaleGroupInclusion :=
  let := picardCommGrpObj X.hom P R
  let G := (groupSchemeBaseChange f).functor
  G.map (picardIdentityComponentGroupInclusion P R) ≫
    (picardRepresenterGroupBaseChangeIso P R f).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original group inclusion retains the underlying original Jacobian morphism. -/
theorem picardDegreeZeroEtaleGroupInclusion_hom :
    letI := picardCommGrpObj X.hom P R
    let G := (groupSchemeBaseChange f).functor
    (picardDegreeZeroEtaleGroupInclusion P R f).hom.hom =
      (G.map (picardIdentityComponentGroupInclusion P R)).hom.hom := by
  dsimp only
  let := picardCommGrpObj X.hom P R
  let G := (groupSchemeBaseChange f).functor
  let i := G.map (picardIdentityComponentGroupInclusion P R)
  let e := picardRepresenterGroupBaseChangeIso P R f
  have h := picardRepresenterGroupBaseChangeIso_hom_identity P R f
  change i.hom.hom ≫ e.hom.hom.hom = i.hom.hom
  exact (congrArg (fun f' => i.hom.hom ≫ f') h).trans (Category.comp_id _)

omit [IsLocallyNoetherian S] in
include hX in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual prime-to-characteristic multiplication on the base-changed
Jacobian is epic on its original represented étale sheaf. -/
theorem epi_nsmul_representedJacobianBaseChange [IsSeparated P.obj.hom]
    (n : ℕ) (hunit : IsUnit (n : k)) :
    letI := picardCommGrpObj X.hom P R
    let J := picardIdentityComponent X.hom P R
    letI : IsCommMonObj J := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
    let JG := Grp.mk J
    Epi (n • 𝟙 (representedSheaf ((groupSchemeBaseChange f).functor.obj JG))) := by
  dsimp only
  let := picardCommGrpObj X.hom P R
  let J := picardIdentityComponent X.hom P R
  let : IsCommMonObj J := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
  let G := Grp.mk J
  let hh := finite_etale_surjective_multiplication_identityComponentOver hX P R n hunit
  have hPow : (((𝟙 G : G ⟶ G) ^ n).hom.hom : J ⟶ J) = (𝟙 J : J ⟶ J) ^ n := by
    simp only [Grp.Hom.hom_pow, Mon.Hom.hom_pow]
    rfl
  have he : Etale ((𝟙 J : J ⟶ J) ^ n).left := hh.2.1
  have hs : Surjective ((𝟙 J : J ⟶ J) ^ n).left := hh.2.2
  exact epi_nsmul_representedSheaf_groupBaseChange f G n
    ((congrArg (fun q : J ⟶ J => Etale q.left) hPow).mpr he)
    ((congrArg (fun q : J ⟶ J => Surjective q.left) hPow).mpr hs)

section Normalized

variable (o : S ⟶ pullback X.hom f) (ho : o ≫ pullback.snd X.hom f = 𝟙 S)
  [IsProper (pullback.snd X.hom f)] [Flat (pullback.snd X.hom f)]
  [GeometricallyIntegral (pullback.snd X.hom f)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original Jacobian inclusion after base change, evaluated in the
original normalized Picard sheaf. -/
abbrev picardDegreeZeroEtaleInclusion :=
  let := picardCommGrpObj X.hom P R
  let J := picardIdentityComponent X.hom P R
  let : IsCommMonObj J := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
  let Q := LocallyNoetherianOver.baseChange f P
  let hQ := baseChangeRepresentableBy X.hom f P R
  let : LocallyOfFiniteType Q.obj.hom := MorphismProperty.pullback_snd P.obj.hom f inferInstance
  let QLaw := picardCommGrpObj (pullback.snd X.hom f) Q hQ
  let QG := @Grp.mk _ _ _ Q.obj QLaw.toGrpObj
  let : IsCommMonObj QG.X := QLaw.toIsCommMonObj
  let i := picardDegreeZeroEtaleGroupInclusion P R f
  representedSheafMap (K := QG) i ≫
    (Kummer.picardRepresenterNormalizedEtaleIso (pullback.snd X.hom f) o ho Q hQ).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The same original Jacobian inclusion is monic on represented étale sheaves. -/
abbrev picardDegreeZeroEtaleInclusionMono :=
  let := picardCommGrpObj X.hom P R
  let J := picardIdentityComponent X.hom P R
  letI : IsCommMonObj J := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
  let q := picardIdentityComponentGroupInclusion P R
  letI : IsOpenImmersion q.hom.hom.left := isOpenImmersion_picardIdentityComponentι X.hom P R
  let hm : Mono q.hom.hom.left := inferInstance
  letI : Mono q.hom.hom := (Over.forget (Base k)).mono_of_mono_map (f := q.hom.hom) hm
  let hi := (Over.pullback f).map_mono q.hom.hom
  let Q := LocallyNoetherianOver.baseChange f P
  let hQ := baseChangeRepresentableBy X.hom f P R
  letI : LocallyOfFiniteType Q.obj.hom := MorphismProperty.pullback_snd P.obj.hom f inferInstance
  let QLaw := picardCommGrpObj (pullback.snd X.hom f) Q hQ
  let QG := @Grp.mk _ _ _ Q.obj QLaw.toGrpObj
  letI : IsCommMonObj QG.X := QLaw.toIsCommMonObj
  let i := picardDegreeZeroEtaleGroupInclusion P R f
  let e := picardDegreeZeroEtaleGroupInclusion_hom P R f
  letI : Mono i.hom.hom := e.symm ▸ hi
  letI : Mono (representedSheafMap (K := QG) i) := RepresentedKernel.represented_mono i
  let N := Kummer.picardRepresenterNormalizedEtaleIso (pullback.snd X.hom f) o ho Q hQ
  show Mono (representedSheafMap (K := QG) i ≫ N.hom) from inferInstance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The same original group map gives the original normalized Picard chart value. -/
abbrev picardDegreeZeroEtaleInclusionAppOfPoint (U : S.Etale)
    (x :
      letI := picardCommGrpObj X.hom P R
      let J := Grp.mk (picardIdentityComponent X.hom P R)
      (Scheme.Etale.forget S).obj U ⟶ ((groupSchemeBaseChange f).functor.obj J).X) :=
  let := picardCommGrpObj X.hom P R
  let J := picardIdentityComponent X.hom P R
  letI : IsCommMonObj J := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
  let Q := LocallyNoetherianOver.baseChange f P
  let hQ := baseChangeRepresentableBy X.hom f P R
  letI : LocallyOfFiniteType Q.obj.hom := MorphismProperty.pullback_snd P.obj.hom f inferInstance
  let QLaw := picardCommGrpObj (pullback.snd X.hom f) Q hQ
  let QG := @Grp.mk _ _ _ Q.obj QLaw.toGrpObj
  letI : IsCommMonObj QG.X := QLaw.toIsCommMonObj
  let i := picardDegreeZeroEtaleGroupInclusion P R f
  let N := Kummer.picardRepresenterNormalizedEtaleIso (pullback.snd X.hom f) o ho Q hQ
  representedSheafMap_then_apply (H := QG) i N.hom U x

end Normalized

end AlgebraicGeometry.Scheme.OverField.Curve
