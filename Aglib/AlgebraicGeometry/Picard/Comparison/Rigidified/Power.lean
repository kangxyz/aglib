/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Comparison.UniversalRigidified
public import Aglib.AlgebraicGeometry.Picard.PowerBaseChange
public import Aglib.AlgebraicGeometry.Picard.PowerDescent

/-!
# Tensor powers of actual rigidified line bundles

The original bundle power and native powered frame give the origin
rigidification. The pullback and unit comparisons preserve it in every degree.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.RelativePicard.RigidifiedPair

open Scheme.Modules Scheme.Modules.Invertible
open Scheme.Modules.Invertible.PowerBaseChange
open Scheme.Modules.Invertible.PowerDescent
open Scheme.Modules.Invertible.PowerPullback
open Scheme.Modules.Invertible.PowerPullbackNaturality
open Scheme.Modules.Invertible.TrivializedPower
open Scheme.Modules.Invertible.TrivializedPowerTorsor
open Scheme.Modules.Invertible.UnitPower

universe u

-- The source uses the underlying module objects of the same pulled-back bundles.
set_option backward.isDefEq.respectTransparency false in
private theorem powerFrame_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {L M : LineBundle Y} (a : L.val ≅ M.val)
    (e : (Scheme.Modules.pullback f).obj M.val ≅ SheafOfModules.unit X.ringCatSheaf)
    (n : ℕ) :
    (Scheme.Modules.pullback f).mapIso (powerIso Y a n) ≪≫ powerFrame M f e n =
      powerFrame L f ((Scheme.Modules.pullback f).mapIso a ≪≫ e) n := by
  have h := UnitPower.powerIso_trans X (L := pullbackLineBundle f L)
    (M := pullbackLineBundle f M) (N := unitLineBundle X)
    ((Scheme.Modules.pullback f).mapIso a) e n
  unfold powerFrame normalizedPower
  erw [h]
  simpa only [CategoryTheory.Iso.trans_assoc] using congrArg (fun b => b ≪≫
    powerIso X (L := pullbackLineBundle f M) (M := unitLineBundle X) e n ≪≫ unitPowerIso X n)
      (pullbackPowerIso_naturality f a n)

private theorem iso_rearrange {C : Type*} [Category* C] {W X Y Z : C}
    (a : W ≅ X) (b : W ≅ Y) (c : X ≅ Z) (d : Y ≅ Z)
    (h : a.symm ≪≫ b = c ≪≫ d.symm) : b ≪≫ d = a ≪≫ c := by
  apply CategoryTheory.Iso.ext
  have he : a.inv ≫ b.hom = c.hom ≫ d.inv := congrArg CategoryTheory.Iso.hom h
  change b.hom ≫ d.hom = a.hom ≫ c.hom
  calc
    _ = a.hom ≫ (a.inv ≫ b.hom) ≫ d.hom := by
      simp only [Category.assoc, CategoryTheory.Iso.hom_inv_id_assoc]
    _ = _ := by rw [he, Category.assoc, CategoryTheory.Iso.inv_hom_id, Category.comp_id]

-- The comparison uses the native objects of the composite pullback functor.
set_option backward.isDefEq.respectTransparency false in
private theorem pullbackPowerIso_comp_forward {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : LineBundle Z) (n : ℕ) :
    (Scheme.Modules.pullback f).mapIso (pullbackPowerIso g L n) ≪≫
      pullbackPowerIso f (pullbackLineBundle g L) n ≪≫
      powerIso X (L := pullbackLineBundle f (pullbackLineBundle g L))
        (M := pullbackLineBundle (f ≫ g) L) ((Scheme.Modules.pullbackComp f g).app L.val) n =
    (Scheme.Modules.pullbackComp f g).app (tensorPowerLineBundle Z L n).val ≪≫
      pullbackPowerIso (f ≫ g) L n := by
  let a := (Scheme.Modules.pullbackComp f g).app (tensorPowerLineBundle Z L n).val
  let b := (Scheme.Modules.pullback f).mapIso (pullbackPowerIso g L n) ≪≫
    pullbackPowerIso f (pullbackLineBundle g L) n
  let c := pullbackPowerIso (f ≫ g) L n
  let d := powerIso X (L := pullbackLineBundle f (pullbackLineBundle g L))
    (M := pullbackLineBundle (f ≫ g) L) ((Scheme.Modules.pullbackComp f g).app L.val) n
  have h : a.symm ≪≫ b = c ≪≫ d.symm := by
    apply CategoryTheory.Iso.ext
    have hs := congrArg CategoryTheory.Iso.hom (UnitPower.powerIso_symm X
      (L := pullbackLineBundle f (pullbackLineBundle g L))
      (M := pullbackLineBundle (f ≫ g) L) ((Scheme.Modules.pullbackComp f g).app L.val) n)
    have hc := pullbackPowerIso_comp f g L n
    simp only [a, b, c, d, CategoryTheory.Iso.trans_hom, CategoryTheory.Iso.symm_hom,
      CategoryTheory.Functor.mapIso_hom]
    exact hc.trans (congrArg (fun i => (pullbackPowerIso (f ≫ g) L n).hom ≫ i) hs)
  calc
    _ = b ≪≫ d := (CategoryTheory.Iso.trans_assoc _ _ _).symm
    _ = a ≪≫ c := iso_rearrange a b c d h

-- The two power comparisons retain their native pullback module parents.
set_option backward.isDefEq.respectTransparency false in
private theorem powerFrame_pullbackFrame {X U V W : Scheme.{u}} (f : W ⟶ X)
    (L : LineBundle X) (g : U ⟶ X) (s : V ⟶ W) (t : V ⟶ U) (w : t ≫ g = s ≫ f)
    (e : (Scheme.Modules.pullback g).obj L.val ≅ SheafOfModules.unit U.ringCatSheaf)
    (n : ℕ) :
    (Scheme.Modules.pullback s).mapIso (pullbackPowerIso f L n) ≪≫
      powerFrame (pullbackLineBundle f L) s (pullbackFrame f L g s t w e) n =
    pullbackFrame f (tensorPowerLineBundle X L n) g s t w (powerFrame L g e n) := by
  unfold pullbackFrame
  rw [powerFrame_nativePullFrame L g (s ≫ f) t w e n]
  have h := UnitPower.powerIso_trans V (L := pullbackLineBundle s (pullbackLineBundle f L))
    (M := pullbackLineBundle (s ≫ f) L) (N := unitLineBundle V)
    ((Scheme.Modules.pullbackComp s f).app L.val) (nativePullFrame L g (s ≫ f) t w e) n
  unfold powerFrame normalizedPower
  erw [h]
  simpa only [CategoryTheory.Iso.trans_assoc] using congrArg (fun a => a ≪≫
    powerIso V (L := pullbackLineBundle (s ≫ f) L) (M := unitLineBundle V)
      (nativePullFrame L g (s ≫ f) t w e) n ≪≫ unitPowerIso V n)
    (pullbackPowerIso_comp_forward s f L n)

private theorem pullbackCongr_app_symm {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g)
    (M : Y.Modules) : ((Scheme.Modules.pullbackCongr w).app M).symm =
      (Scheme.Modules.pullbackCongr w.symm).app M := by
  subst g
  rfl

private theorem pullbackFrame_whole {X U V W : Scheme.{u}} (f : W ⟶ X)
    (L : LineBundle X) (g : U ⟶ X) (s : V ⟶ W) (t : V ⟶ U) (w : t ≫ g = s ≫ f)
    (e : (Scheme.Modules.pullback g).obj L.val ≅ SheafOfModules.unit U.ringCatSheaf) :
    pullbackFrame f L g s t w e =
      (Scheme.Modules.pullbackComp s f).app L.val ≪≫
      (Scheme.Modules.pullbackCongr w.symm).app L.val ≪≫
      ((Scheme.Modules.pullbackComp t g).app L.val).symm ≪≫
      (Scheme.Modules.pullback t).mapIso e ≪≫ pullbackUnitIso t :=
  congrArg (fun a => (Scheme.Modules.pullbackComp s f).app L.val ≪≫ a ≪≫
    ((Scheme.Modules.pullbackComp t g).app L.val).symm ≪≫
    (Scheme.Modules.pullback t).mapIso e ≪≫ pullbackUnitIso t) (pullbackCongr_app_symm w L.val)

private theorem mapIso_inv_cancel {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B E : C} {U : D} (v : A ≅ B) (e : E ≅ B) (u : F.obj B ≅ U) :
    F.mapIso (v ≪≫ e.symm) ≪≫ (F.mapIso e ≪≫ u) = F.mapIso v ≪≫ u := by
  apply CategoryTheory.Iso.ext
  simp only [CategoryTheory.Iso.trans_hom, CategoryTheory.Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc e.inv e.hom, CategoryTheory.Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

variable {S X : Scheme.{u}} {p : X ⟶ S} {o : S ⟶ X} {ho : o ≫ p = 𝟙 S}
  {T T' : Over S}

/-- The original tensor power with the induced origin rigidification. -/
def power (Q : RigidifiedPair p o ho T) (n : ℕ) : RigidifiedPair p o ho T where
  bundle := tensorPowerLineBundle _ Q.bundle n
  rigidification := powerFrame Q.bundle (originSection p o ho T) Q.rigidification n

/-- The powered rigidification is the original power of the actual origin frame. -/
theorem power_rigidification (Q : RigidifiedPair p o ho T) (n : ℕ) :
    (Q.power n).rigidification =
      powerFrame Q.bundle (originSection p o ho T) Q.rigidification n := rfl

/-- The actual powered bundle has the corresponding Picard class. -/
theorem classOf_power (Q : RigidifiedPair p o ho T) (n : ℕ) :
    classOf _ (Q.power n).bundle = n • classOf _ Q.bundle :=
  classOf_tensorPower _ Q.bundle n

/-- The original power of a rigidified isomorphism preserves the powered frames. -/
def Iso.power {Q Q' : RigidifiedPair p o ho T} (e : Iso Q Q') (n : ℕ) :
    Iso (Q.power n) (Q'.power n) where
  iso := powerIso _ (L := Q.bundle) (M := Q'.bundle) e.iso n
  comm := by
    have h := powerFrame_iso (originSection p o ho T) e.iso Q'.rigidification n
    have he : (Scheme.Modules.pullback (originSection p o ho T)).mapIso e.iso ≪≫
        Q'.rigidification = Q.rigidification := CategoryTheory.Iso.ext e.comm
    exact congrArg CategoryTheory.Iso.hom (h.trans (congrArg
      (fun a => powerFrame Q.bundle (originSection p o ho T) a n) he))

-- The origin comparison uses the original pullback functors on module sheaves.
set_option backward.isDefEq.respectTransparency false in
private theorem map_rigidification_pullbackFrame (f : T' ⟶ T) (Q : RigidifiedPair p o ho T) :
    (map f Q).rigidification =
      pullbackFrame ((familyScheme p).map f) Q.bundle (originSection p o ho T)
        (originSection p o ho T') f.left
        (originSection_comp_familyScheme_map (p := p) (o := o) (ho := ho) f).symm
        Q.rigidification :=
  (pullbackFrame_whole ((familyScheme p).map f) Q.bundle (originSection p o ho T)
    (originSection p o ho T') f.left
    (originSection_comp_familyScheme_map (p := p) (o := o) (ho := ho) f).symm
    Q.rigidification).symm

/-- Pullback preserves the original rigidified tensor power. Its bundle map is
exactly the native tensor-power pullback comparison. -/
def mapPowerIso (f : T' ⟶ T) (Q : RigidifiedPair p o ho T) (n : ℕ) :
    Iso (map f (Q.power n)) ((map f Q).power n) where
  iso := pullbackPowerIso ((familyScheme p).map f) Q.bundle n
  comm := by
    have h := powerFrame_pullbackFrame ((familyScheme p).map f) Q.bundle
      (originSection p o ho T) (originSection p o ho T') f.left
      (originSection_comp_familyScheme_map (p := p) (o := o) (ho := ho) f).symm
      Q.rigidification n
    have hs := congrArg (fun e =>
      (Scheme.Modules.pullback (originSection p o ho T')).mapIso
        (pullbackPowerIso ((familyScheme p).map f) Q.bundle n) ≪≫
      powerFrame (pullbackLineBundle ((familyScheme p).map f) Q.bundle)
        (originSection p o ho T') e n) (map_rigidification_pullbackFrame f Q)
    exact congrArg CategoryTheory.Iso.hom
      (hs.trans (h.trans (map_rigidification_pullbackFrame f (Q.power n)).symm))

/-- The trivial rigidified pair's power has its canonical unit isomorphism. -/
def trivialPowerIso (T : Over S) (n : ℕ) :
    Iso ((trivialRigidifiedPair p o ho T).power n) (trivialRigidifiedPair p o ho T) where
  iso := normalizedPower (L := trivialLineBundle _) (freeUnitIso _) n ≪≫ (freeUnitIso _).symm
  comm := by
    let f := originSection p o ho T
    let Y := pullback p T.hom
    let e := freeUnitIso Y
    let v := normalizedPower (L := trivialLineBundle Y) e n
    change (Scheme.Modules.pullback f).map (v ≪≫ e.symm).hom ≫
      ((Scheme.Modules.pullback f).mapIso e ≪≫ pullbackUnitIso f).hom =
      (powerFrame (trivialLineBundle Y) f
        ((Scheme.Modules.pullback f).mapIso e ≪≫ pullbackUnitIso f) n).hom
    calc
      _ = (Scheme.Modules.pullback f).map v.hom ≫ (pullbackUnitIso f).hom :=
        congrArg CategoryTheory.Iso.hom
          (mapIso_inv_cancel (Scheme.Modules.pullback f) v e (pullbackUnitIso f))
      _ = _ := (normalizedPower_pullback f (L := trivialLineBundle Y) e n).symm

end AlgebraicGeometry.Scheme.RelativePicard.RigidifiedPair
