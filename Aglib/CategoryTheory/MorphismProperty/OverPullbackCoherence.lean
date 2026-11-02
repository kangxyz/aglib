/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-! # Coherence of the actual restricted Over pullback comparisons

The native pullback, compositor, equality transports and original projections
are retained. Pullback and stability assumptions are per actual base arrow.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.MorphismProperty.Over

universe u v

variable {C : Type u} [Category.{v} C] {P Q : MorphismProperty C}
  [Q.IsMultiplicative] [Q.RespectsIso] [Q.IsStableUnderBaseChange]

/-- Equality of the actual base arrows identifies the original pullback functors. -/
theorem pullbackFunctorEq (P Q : MorphismProperty C)
    [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]
    {X S : C} {f g : S ⟶ X}
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f]
    [P.HasPullbacksAlong g] [P.IsStableUnderBaseChangeAlong g]
    (h : f = g) : pullback P Q f = pullback P Q g := by
  subst g
  rfl

/-- Equality of the original base arrows identifies their actual pullback objects.
The equality proof carries no additional choice of pullback realization. -/
theorem pullbackObjectEq (P Q : MorphismProperty C)
    [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]
    {X S : C} {f g : S ⟶ X}
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f]
    [P.HasPullbacksAlong g] [P.IsStableUnderBaseChangeAlong g]
    (h : f = g) (U : P.Over Q X) :
    (pullback P Q f).obj U = (pullback P Q g).obj U :=
  congrArg (fun F => F.obj U) (pullbackFunctorEq P Q h)

/-- The original compositor, with base arrows in geometric composition order. -/
abbrev pullbackCompositionIso {X S T : C} (P Q : MorphismProperty C)
    [Q.IsMultiplicative] [Q.RespectsIso] [Q.IsStableUnderBaseChange]
    (f : S ⟶ X) (g : T ⟶ S)
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f]
    [P.HasPullbacksAlong g] [P.IsStableUnderBaseChangeAlong g] :
    pullback P Q (g ≫ f) ≅ pullback P Q f ⋙ pullback P Q g :=
  pullbackComp g f

/-- The actual identity comparison has the original first pullback projection. -/
def pullbackIdentityIso (P Q : MorphismProperty C)
    [Q.IsMultiplicative] [Q.RespectsIso] [Q.IsStableUnderBaseChange]
    (X : C) [P.HasPullbacksAlong (𝟙 X)] [P.IsStableUnderBaseChangeAlong (𝟙 X)] :
    pullback P Q (𝟙 X) ≅ 𝟭 (P.Over Q X) :=
  NatIso.ofComponents
    (fun U => MorphismProperty.Over.isoMk (asIso (Limits.pullback.fst U.hom (𝟙 X)))
      (by simpa using Limits.pullback.condition (f := U.hom) (g := 𝟙 X)))
    (fun q => by
      apply MorphismProperty.Over.Hom.ext
      change Limits.pullback.lift _ _ _ ≫ Limits.pullback.fst _ _ =
        Limits.pullback.fst _ _ ≫ q.left
      simp only [Limits.pullback.lift_fst])

omit [Q.RespectsIso] in
/-- Transport along equality of base maps preserves the first pullback projection. -/
@[reassoc]
theorem pullbackCoherence_eqToHom_fst {X S : C} {f g : S ⟶ X}
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f]
    [P.HasPullbacksAlong g] [P.IsStableUnderBaseChangeAlong g] (h : f = g) (U : P.Over Q X) :
    (eqToHom (pullbackObjectEq P Q h U)).left ≫
        Limits.pullback.fst U.hom g = Limits.pullback.fst U.hom f := by
  subst g
  change (𝟙 _) ≫ Limits.pullback.fst U.hom f = _
  exact Category.id_comp _

omit [Q.RespectsIso] in
/-- Transport along equality of base maps preserves the structural pullback projection. -/
@[reassoc]
theorem pullbackCoherence_eqToHom_snd {X S : C} {f g : S ⟶ X}
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f]
    [P.HasPullbacksAlong g] [P.IsStableUnderBaseChangeAlong g] (h : f = g) (U : P.Over Q X) :
    (eqToHom (pullbackObjectEq P Q h U)).left ≫
        Limits.pullback.snd U.hom g = Limits.pullback.snd U.hom f := by
  subst g
  change (𝟙 _) ≫ Limits.pullback.snd U.hom f = _
  exact Category.id_comp _

omit [Q.RespectsIso] [Q.IsStableUnderBaseChange] in
/-- Underlying maps of composable restricted Over arrows compose without extra transports. -/
@[simp]
theorem overCoherenceHom_comp_left {X : C} {U V W : P.Over Q X}
    (a : U ⟶ V) (b : V ⟶ W) : (a ≫ b).left = a.left ≫ b.left := rfl

omit [Q.RespectsIso] [Q.IsStableUnderBaseChange] in
/-- The underlying map of the identity restricted Over arrow. -/
@[simp]
theorem overCoherenceHom_id_left {X : C} (U : P.Over Q X) :
    (𝟙 U : U ⟶ U).left = 𝟙 U.left := rfl

omit [Q.RespectsIso] in
/-- The structural arrow of the original base-changed restricted Over object. -/
@[simp]
theorem pullbackCoherence_obj_hom {X S : C} (f : S ⟶ X)
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f] (U : P.Over Q X) :
    ((pullback P Q f).obj U).hom = Limits.pullback.snd U.hom f := rfl

omit [Q.RespectsIso] in
/-- The first projection of the original restricted Over base-change map. -/
@[reassoc]
theorem pullbackCoherence_map_fst {X S : C} (f : S ⟶ X)
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f]
    {U V : P.Over Q X} (a : U ⟶ V) :
    ((pullback P Q f).map a).left ≫ Limits.pullback.fst V.hom f =
      Limits.pullback.fst U.hom f ≫ a.left := by
  change Limits.pullback.lift _ _ _ ≫ Limits.pullback.fst _ _ = _
  exact Limits.pullback.lift_fst _ _ _

omit [Q.RespectsIso] in
/-- The structural projection of the original restricted Over base-change map. -/
@[reassoc]
theorem pullbackCoherence_map_snd {X S : C} (f : S ⟶ X)
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f]
    {U V : P.Over Q X} (a : U ⟶ V) :
    ((pullback P Q f).map a).left ≫ Limits.pullback.snd V.hom f = Limits.pullback.snd U.hom f := by
  change Limits.pullback.lift _ _ _ ≫ Limits.pullback.snd _ _ = _
  exact Limits.pullback.lift_snd _ _ _

/-- The original composition comparison preserves the projection to the original object. -/
@[reassoc]
theorem pullbackCompositionIso_hom_fst_fst {X S T : C}
    (f : S ⟶ X) (g : T ⟶ S)
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f]
    [P.HasPullbacksAlong g] [P.IsStableUnderBaseChangeAlong g] (U : P.Over Q X) :
    ((pullbackCompositionIso P Q f g).hom.app U).left ≫
        Limits.pullback.fst (Limits.pullback.snd U.hom f) g ≫ Limits.pullback.fst U.hom f =
      Limits.pullback.fst U.hom (g ≫ f) :=
  MorphismProperty.Over.pullbackComp_left_fst_fst g f U

/-- The middle structural projection of the original composition comparison. -/
@[reassoc]
theorem pullbackCompositionIso_hom_fst_snd {X S T : C}
    (f : S ⟶ X) (g : T ⟶ S)
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f]
    [P.HasPullbacksAlong g] [P.IsStableUnderBaseChangeAlong g] (U : P.Over Q X) :
    ((pullbackCompositionIso P Q f g).hom.app U).left ≫
        Limits.pullback.fst (Limits.pullback.snd U.hom f) g ≫ Limits.pullback.snd U.hom f =
      Limits.pullback.snd U.hom (g ≫ f) ≫ g := by
  simp [pullbackCompositionIso]

/-- The final structural projection of the original composition comparison. -/
@[reassoc]
theorem pullbackCompositionIso_hom_snd {X S T : C}
    (f : S ⟶ X) (g : T ⟶ S)
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f]
    [P.HasPullbacksAlong g] [P.IsStableUnderBaseChangeAlong g] (U : P.Over Q X) :
    ((pullbackCompositionIso P Q f g).hom.app U).left ≫
        Limits.pullback.snd (Limits.pullback.snd U.hom f) g = Limits.pullback.snd U.hom (g ≫ f) :=
  MorphismProperty.Over.w ((pullbackCompositionIso P Q f g).hom.app U)

/-- The identity pullback comparison is its original first pullback projection. -/
@[simp]
theorem pullbackIdentityIso_hom_left (X : C)
    [P.HasPullbacksAlong (𝟙 X)] [P.IsStableUnderBaseChangeAlong (𝟙 X)] (U : P.Over Q X) :
    ((pullbackIdentityIso P Q X).hom.app U).left = Limits.pullback.fst U.hom (𝟙 X) := rfl

/-- The original restricted Over pullback comparisons satisfy associativity on every object. -/
@[reassoc]
theorem pullbackCompositionIso_assoc {X S T V : C}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T)
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f]
    [P.HasPullbacksAlong g] [P.IsStableUnderBaseChangeAlong g]
    [P.HasPullbacksAlong h] [P.IsStableUnderBaseChangeAlong h] (U : P.Over Q X) :
    (pullbackCompositionIso P Q f (h ≫ g)).hom.app U ≫
        (pullbackCompositionIso P Q g h).hom.app ((pullback P Q f).obj U) =
      (eqToIso (pullbackObjectEq P Q (Category.assoc h g f) U)).hom ≫
        (pullbackCompositionIso P Q (g ≫ f) h).hom.app U ≫
        (pullback P Q h).map ((pullbackCompositionIso P Q f g).hom.app U) := by
  have hff := pullbackCompositionIso_hom_fst_fst (P := P) (Q := Q) g h ((pullback P Q f).obj U)
  have hfs := pullbackCompositionIso_hom_fst_snd (P := P) (Q := Q) g h ((pullback P Q f).obj U)
  have hs := pullbackCompositionIso_hom_snd (P := P) (Q := Q) g h ((pullback P Q f).obj U)
  simp only [pullbackCoherence_obj_hom] at hff hfs hs
  have hfff := congrArg (fun a => a ≫ Limits.pullback.fst U.hom f) hff
  have hffs := congrArg (fun a => a ≫ Limits.pullback.snd U.hom f) hff
  simp only [Category.assoc] at hfff hffs
  have hMF := pullbackCoherence_map_fst (P := P) (Q := Q) h
    ((pullbackCompositionIso P Q f g).hom.app U)
  have hMS := pullbackCoherence_map_snd (P := P) (Q := Q) h
    ((pullbackCompositionIso P Q f g).hom.app U)
  simp only [Functor.comp_obj, pullbackCoherence_obj_hom] at hMF hMS
  have hMFF := congrArg (fun a => a ≫ Limits.pullback.fst (Limits.pullback.snd U.hom f) g ≫
    Limits.pullback.fst U.hom f) hMF
  have hMFS := congrArg (fun a => a ≫ Limits.pullback.fst (Limits.pullback.snd U.hom f) g ≫
    Limits.pullback.snd U.hom f) hMF
  have hMSF := congrArg (fun a => a ≫ Limits.pullback.snd (Limits.pullback.snd U.hom f) g) hMF
  simp only [Category.assoc, pullbackCompositionIso_hom_fst_fst] at hMFF
  simp only [Category.assoc, pullbackCompositionIso_hom_fst_snd] at hMFS
  simp only [Category.assoc, pullbackCompositionIso_hom_snd] at hMSF
  have hCF := pullbackCompositionIso_hom_fst_fst (P := P) (Q := Q) (g ≫ f) h U
  have hCFS := pullbackCompositionIso_hom_fst_snd (P := P) (Q := Q) (g ≫ f) h U
  have hCS := pullbackCompositionIso_hom_snd (P := P) (Q := Q) (g ≫ f) h U
  have hCFSg := congrArg (fun a => a ≫ g) hCFS
  simp only [Category.assoc] at hCFSg
  have htF := pullbackCoherence_eqToHom_fst (P := P) (Q := Q) (Category.assoc h g f) U
  have htS := pullbackCoherence_eqToHom_snd (P := P) (Q := Q) (Category.assoc h g f) U
  have htSh := congrArg (fun a => a ≫ h) htS
  have htShg := congrArg (fun a => a ≫ h ≫ g) htS
  simp only [Category.assoc] at htSh htShg
  apply MorphismProperty.Over.Hom.ext
  simp only [overCoherenceHom_comp_left]
  apply Limits.pullback.hom_ext
  · apply Limits.pullback.hom_ext
    · apply Limits.pullback.hom_ext
      · simp only [Category.assoc, pullbackCoherence_obj_hom, eqToIso.hom,
          pullbackCompositionIso_hom_fst_fst, hfff]
        rw [hMFF, hCF]
        exact htF.symm
      · simp only [Category.assoc, pullbackCoherence_obj_hom, eqToIso.hom,
          pullbackCompositionIso_hom_fst_snd, hffs]
        rw [hMFS, hCFSg]
        exact htShg.symm
    · simp only [Category.assoc, pullbackCoherence_obj_hom, eqToIso.hom,
        pullbackCompositionIso_hom_snd_assoc, hfs]
      rw [hMSF, hCFS]
      exact htSh.symm
  · simp only [Category.assoc, pullbackCoherence_obj_hom, eqToIso.hom,
      pullbackCompositionIso_hom_snd, hs]
    rw [hMS, hCS]
    exact htS.symm

/-- The pullback comparison with an identity in the second position is normalized by
its original pullback projection. -/
@[reassoc]
theorem pullbackCompositionIso_comp_id {X S : C} (f : S ⟶ X)
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f]
    [P.HasPullbacksAlong (𝟙 S)] [P.IsStableUnderBaseChangeAlong (𝟙 S)] (U : P.Over Q X) :
    (pullbackCompositionIso P Q f (𝟙 S)).hom.app U ≫
        (pullbackIdentityIso P Q S).hom.app ((pullback P Q f).obj U) =
      eqToHom (pullbackObjectEq P Q (Category.id_comp f) U) := by
  apply MorphismProperty.Over.Hom.ext
  simp only [overCoherenceHom_comp_left, pullbackIdentityIso_hom_left]
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, pullbackCoherence_obj_hom,
      pullbackCompositionIso_hom_fst_fst]
    exact (pullbackCoherence_eqToHom_fst (P := P) (Q := Q) (Category.id_comp f) U).symm
  · simp only [Category.assoc, pullbackCoherence_obj_hom,
      pullbackCompositionIso_hom_fst_snd, Category.comp_id]
    exact (pullbackCoherence_eqToHom_snd (P := P) (Q := Q) (Category.id_comp f) U).symm

/-- The pullback comparison with an identity in the first position is normalized by
its original pullback projection. -/
@[reassoc]
theorem pullbackCompositionIso_id_comp {X S : C} (f : S ⟶ X)
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f]
    [P.HasPullbacksAlong (𝟙 X)] [P.IsStableUnderBaseChangeAlong (𝟙 X)] (U : P.Over Q X) :
    (pullbackCompositionIso P Q (𝟙 X) f).hom.app U ≫
        (pullback P Q f).map ((pullbackIdentityIso P Q X).hom.app U) =
      eqToHom (pullbackObjectEq P Q (Category.comp_id f) U) := by
  apply MorphismProperty.Over.Hom.ext
  simp only [overCoherenceHom_comp_left]
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, pullbackCoherence_map_fst, pullbackIdentityIso_hom_left,
      pullbackCoherence_obj_hom,
      pullbackCompositionIso_hom_fst_fst]
    exact (pullbackCoherence_eqToHom_fst (P := P) (Q := Q) (Category.comp_id f) U).symm
  · simp only [Category.assoc, pullbackCoherence_map_snd, pullbackCoherence_obj_hom,
      pullbackCompositionIso_hom_snd]
    exact (pullbackCoherence_eqToHom_snd (P := P) (Q := Q) (Category.comp_id f) U).symm

/-- The actual restricted pullback compositor satisfies the whole associativity law. -/
theorem pullbackCompositionIso_assoc_whole {X S T V : C}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T)
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f]
    [P.HasPullbacksAlong g] [P.IsStableUnderBaseChangeAlong g]
    [P.HasPullbacksAlong h] [P.IsStableUnderBaseChangeAlong h] :
    (pullbackCompositionIso P Q f (h ≫ g)).hom ≫
        Functor.whiskerLeft (pullback P Q f) (pullbackCompositionIso P Q g h).hom ≫
        (Functor.associator (pullback P Q f) (pullback P Q g) (pullback P Q h)).inv =
      (eqToIso (pullbackFunctorEq P Q (Category.assoc h g f))).hom ≫
        (pullbackCompositionIso P Q (g ≫ f) h).hom ≫
        Functor.whiskerRight (pullbackCompositionIso P Q f g).hom (pullback P Q h) := by
  apply NatTrans.ext
  funext U
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.comp_id, eqToIso.hom, eqToHom_app] using
      pullbackCompositionIso_assoc (P := P) (Q := Q) f g h U

/-- The whole actual right unit retains the original equality transport. -/
theorem pullbackCompositionIso_comp_id_whole {X S : C} (f : S ⟶ X)
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f]
    [P.HasPullbacksAlong (𝟙 S)] [P.IsStableUnderBaseChangeAlong (𝟙 S)] :
    (pullbackCompositionIso P Q f (𝟙 S)).hom ≫
        Functor.whiskerLeft (pullback P Q f) (pullbackIdentityIso P Q S).hom ≫
        (Functor.rightUnitor (pullback P Q f)).hom =
      (eqToIso (pullbackFunctorEq P Q (Category.id_comp f))).hom := by
  apply NatTrans.ext
  funext U
  have hu := pullbackCompositionIso_comp_id (P := P) (Q := Q) f U
  have hunit : (pullbackCompositionIso P Q f (𝟙 S)).hom.app U ≫
      (pullbackIdentityIso P Q S).hom.app ((pullback P Q f).obj U) ≫ 𝟙 ((pullback P Q f).obj U) =
      eqToHom (pullbackObjectEq P Q (Category.id_comp f) U) := by
    calc
      _ = ((pullbackCompositionIso P Q f (𝟙 S)).hom.app U ≫
          (pullbackIdentityIso P Q S).hom.app ((pullback P Q f).obj U)) ≫
          𝟙 ((pullback P Q f).obj U) :=
        (Category.assoc _ _ _).symm
      _ = eqToHom (pullbackObjectEq P Q (Category.id_comp f) U) ≫
          𝟙 ((pullback P Q f).obj U) := congrArg
        (fun k : ((pullback P Q (𝟙 S ≫ f)).obj U) ⟶ ((pullback P Q f).obj U) =>
          k ≫ 𝟙 ((pullback P Q f).obj U)) hu
      _ = _ := Category.comp_id _
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, eqToIso.hom, eqToHom_app] using hunit

/-- The whole actual left unit retains the original equality transport. -/
theorem pullbackCompositionIso_id_comp_whole {X S : C} (f : S ⟶ X)
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f]
    [P.HasPullbacksAlong (𝟙 X)] [P.IsStableUnderBaseChangeAlong (𝟙 X)] :
    (pullbackCompositionIso P Q (𝟙 X) f).hom ≫
        Functor.whiskerRight (pullbackIdentityIso P Q X).hom (pullback P Q f) ≫
        (Functor.leftUnitor (pullback P Q f)).hom =
      (eqToIso (pullbackFunctorEq P Q (Category.comp_id f))).hom := by
  apply NatTrans.ext
  funext U
  have hu := pullbackCompositionIso_id_comp (P := P) (Q := Q) f U
  have hunit : (pullbackCompositionIso P Q (𝟙 X) f).hom.app U ≫
      (pullback P Q f).map ((pullbackIdentityIso P Q X).hom.app U) ≫ 𝟙 ((pullback P Q f).obj U) =
      eqToHom (pullbackObjectEq P Q (Category.comp_id f) U) := by
    calc
      _ = ((pullbackCompositionIso P Q (𝟙 X) f).hom.app U ≫
          (pullback P Q f).map ((pullbackIdentityIso P Q X).hom.app U)) ≫
          𝟙 ((pullback P Q f).obj U) :=
        (Category.assoc _ _ _).symm
      _ = eqToHom (pullbackObjectEq P Q (Category.comp_id f) U) ≫
          𝟙 ((pullback P Q f).obj U) := congrArg
        (fun k : ((pullback P Q (f ≫ 𝟙 X)).obj U) ⟶ ((pullback P Q f).obj U) =>
          k ≫ 𝟙 ((pullback P Q f).obj U)) hu
      _ = _ := Category.comp_id _
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, eqToIso.hom, eqToHom_app] using hunit

end CategoryTheory.MorphismProperty.Over
