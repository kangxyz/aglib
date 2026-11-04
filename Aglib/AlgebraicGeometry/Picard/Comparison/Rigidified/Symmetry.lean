/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Comparison.Rigidified.Power
public import Aglib.AlgebraicGeometry.Modules.Pullback.Triangle

/-!
# Restriction of normalized line-bundle isomorphisms

Restriction follows the original pullback triangle and frame comparison.
Global scalar detection compares actual isomorphisms at a section, and a
rigidified trivialization gives the original frame at the common origin.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules Scheme.Modules.Invertible
open Scheme.Modules.Invertible.PowerPullback
open Scheme.Modules.Invertible.TrivializedPowerTorsor

universe u

/-- A section of a proper flat geometrically integral morphism detects
global functions over a locally Noetherian base. -/
theorem section_appTop_injective {S X : Scheme.{u}} [IsLocallyNoetherian S]
    (p : X ⟶ S) [IsProper p] [Flat p] [GeometricallyIntegral p]
    (o : S ⟶ X) (ho : o ≫ p = 𝟙 S) : Function.Injective o.appTop := by
  have hq := bijective_app_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral p (𝟙 S) ⊤
  change Function.Bijective (pullback.snd p (𝟙 S)).appTop at hq
  have he : pullback.fst p (𝟙 S) ≫ p = pullback.snd p (𝟙 S) := by
    rw [pullback.condition, Category.comp_id]
  rw [← he, Scheme.Hom.comp_appTop] at hq
  have hf : Function.Bijective (pullback.fst p (𝟙 S)).appTop := by
    change Function.Bijective (Scheme.Γ.map (pullback.fst p (𝟙 S)).op).hom
    exact ConcreteCategory.bijective_of_isIso (Scheme.Γ.map (pullback.fst p (𝟙 S)).op)
  have hp : Function.Surjective p.appTop := by
    intro a
    obtain ⟨b, hb⟩ := hq.surjective ((pullback.fst p (𝟙 S)).appTop a)
    exact ⟨b, hf.injective hb⟩
  have hu : Function.LeftInverse o.appTop p.appTop := by
    intro x
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ho, Scheme.Hom.id_appTop]
    rfl
  intro a b hab
  obtain ⟨x, rfl⟩ := hp a
  obtain ⟨y, rfl⟩ := hp b
  exact congrArg p.appTop ((hu x).symm.trans (hab.trans (hu y)))

set_option backward.isDefEq.respectTransparency false in
/-- A line-bundle isomorphism is determined by its restriction along a map
that detects global scalars, when the source has a frame there. -/
theorem lineBundleIso_eq_of_pullbackMap_eq {S X : Scheme.{u}} (o : S ⟶ X)
    (ho : Function.Injective o.appTop) {L M : LineBundle X}
    (u : (Scheme.Modules.pullback o).obj L.val ≅ SheafOfModules.unit S.ringCatSheaf)
    (e e' : L.val ≅ M.val)
    (h : (Scheme.Modules.pullback o).map e.hom = (Scheme.Modules.pullback o).map e'.hom) : e = e'
      := by
  obtain ⟨r, hr⟩ := exists_eq_globalScalarEndomorphism_of_isLocallyRankOne L.property
    (e.hom ≫ e'.inv)
  have he : (Scheme.Modules.pullback o).map (e.hom ≫ e'.inv) = 𝟙 _ := by
    rw [CategoryTheory.Functor.map_comp, h, ← CategoryTheory.Functor.map_comp,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  rw [hr, pullback_map_globalScalarEndomorphism] at he
  have h1 : globalScalarEndomorphism S ((Scheme.Modules.pullback o).obj L.val)
      (o.appTop 1) = 𝟙 _ := by rw [map_one, globalScalarEndomorphism_one]
  have hr' : r = 1 := ho ((globalScalarEndomorphism_injective_of_iso u) (he.trans h1.symm))
  subst r
  rw [globalScalarEndomorphism_one] at hr
  apply Iso.ext
  apply (cancel_mono e'.inv).mp
  exact hr.trans e'.hom_inv_id.symm

/-- Pull back an actual isomorphism into a pullback and compose through the
specified original triangle. -/
def restrictPullbackIso {X Y Z : Scheme.{u}} (a : Y ⟶ X) (s : X ⟶ Z) (b : Y ⟶ Z)
    (h : a ≫ s = b) {L : X.Modules} {M : Z.Modules}
    (e : L ≅ (Scheme.Modules.pullback s).obj M) : (Scheme.Modules.pullback a).obj L ≅
      (Scheme.Modules.pullback b).obj M :=
  (Scheme.Modules.pullback a).mapIso e ≪≫ (pullbackTriangleIso a s b h).app M

set_option backward.isDefEq.respectTransparency false in
/-- Further restriction of the actual isomorphism through the original
triangle comparisons. -/
theorem restrictPullbackIso_map_hom {X Y Z T : Scheme.{u}} (a : Y ⟶ X) (s : X ⟶ Z)
    (b : Y ⟶ Z) (h : a ≫ s = b) {L : X.Modules} {M : Z.Modules}
    (e : L ≅ (Scheme.Modules.pullback s).obj M) (f : T ⟶ Y) (a' : T ⟶ X) (ha : f ≫ a = a')
    (b' : T ⟶ Z) (hb : f ≫ b = b') :
    (Scheme.Modules.pullback f).map (restrictPullbackIso a s b h e).hom =
      (pullbackTriangleIso f a a' ha).hom.app L ≫
        (restrictPullbackIso a' s b' (by rw [← ha, Category.assoc, h, hb]) e).hom ≫
        (pullbackTriangleIso f b b' hb).inv.app M := by
  have hn := (pullbackTriangleIso f a a' ha).hom.naturality e.hom
  simp only [Functor.comp_map] at hn
  simp only [restrictPullbackIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp]
  rw [pullback_map_pullbackTriangleIso_hom_app f a s ha h hb M,
    reassoc_of% hn]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- An actual isomorphism into a pullback is the identity on a fixed locus
when its restriction at the specified point is the identity. -/
theorem restrictPullbackIso_fixed_eq_refl_of_point {X Y T : Scheme.{u}} (L : LineBundle X)
    (s : X ⟶ X) (e : L.val ≅ (Scheme.Modules.pullback s).obj L.val)
    (d : Y ⟶ X) (hd : d ≫ s = d) (o : T ⟶ Y) (z : T ⟶ X) (ho : o ≫ d = z)
    (hz : z ≫ s = z) (hi : Function.Injective o.appTop)
    (v : (Scheme.Modules.pullback z).obj L.val ≅ SheafOfModules.unit T.ringCatSheaf)
    (he : restrictPullbackIso z s z hz e = CategoryTheory.Iso.refl _) :
    restrictPullbackIso d s d hd e = CategoryTheory.Iso.refl _ := by
  let c := (pullbackTriangleIso o d z ho).app L.val
  apply lineBundleIso_eq_of_pullbackMap_eq o hi
    (L := pullbackLineBundle d L) (M := pullbackLineBundle d L) (c ≪≫ v)
  have h := restrictPullbackIso_map_hom d s d hd e o z ho z ho
  rw [he] at h
  have hc : c.hom ≫ 𝟙 _ ≫ c.inv = 𝟙 _ :=
    (congrArg (fun g => c.hom ≫ g) (Category.id_comp c.inv)).trans c.hom_inv_id
  exact h.trans (hc.trans ((Scheme.Modules.pullback o).map_id _).symm)

set_option backward.isDefEq.respectTransparency false in
/-- A fixed-locus identity restricts along arbitrary actual test maps. -/
theorem restrictPullbackIso_fixed_eq_refl_pullback {X Y T : Scheme.{u}}
    (s : X ⟶ X) {M : X.Modules} (e : M ≅ (Scheme.Modules.pullback s).obj M)
    (d : Y ⟶ X) (hd : d ≫ s = d) (x : T ⟶ Y) (r : T ⟶ X) (hr : x ≫ d = r)
    (hs : r ≫ s = r) (he : restrictPullbackIso d s d hd e = CategoryTheory.Iso.refl _) :
    restrictPullbackIso r s r hs e = CategoryTheory.Iso.refl _ := by
  let c := (pullbackTriangleIso x d r hr).app M
  have h := restrictPullbackIso_map_hom d s d hd e x r hr r hr
  rw [he, CategoryTheory.Iso.refl_hom, CategoryTheory.Functor.map_id] at h
  apply CategoryTheory.Iso.ext
  apply (cancel_epi c.hom).mp
  apply (cancel_mono c.inv).mp
  have hc : (c.hom ≫ 𝟙 _) ≫ c.inv = 𝟙 _ :=
    (congrArg (fun g => g ≫ c.inv) (Category.comp_id c.hom)).trans c.hom_inv_id
  exact (Category.assoc _ _ _).trans (h.symm.trans hc.symm)

set_option backward.isDefEq.respectTransparency false in
private theorem nativePullFrame_hom_triangle {X Y Z : Scheme.{u}} (L : LineBundle X)
    (p : Y ⟶ X) (q : Z ⟶ X) (f : Z ⟶ Y) (w : f ≫ p = q)
    (v : (Scheme.Modules.pullback p).obj L.val ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (nativePullFrame L p q f w v).hom =
      (pullbackTriangleIso f p q w).inv.app L.val ≫ (Scheme.Modules.pullback f).map v.hom ≫
        (pullbackUnitIso f).hom := by
  simp only [nativePullFrame, pullbackTriangleIso_inv_app, Iso.trans_hom,
    Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a frame after the actual triangle isomorphism agrees with
restricting the isomorphism and the frame along the same triangles. -/
theorem nativePullFrame_restrictPullbackIso {X Y Z T : Scheme.{u}}
    (a : Y ⟶ X) (s : X ⟶ Z) (b : Y ⟶ Z) (h : a ≫ s = b) (L : LineBundle X)
    (M : LineBundle Z) (e : L.val ≅ (Scheme.Modules.pullback s).obj M.val)
    (v : (Scheme.Modules.pullback b).obj M.val ≅ SheafOfModules.unit Y.ringCatSheaf)
    (f : T ⟶ Y) (a' : T ⟶ X) (ha : f ≫ a = a') (b' : T ⟶ Z) (hb : f ≫ b = b') :
    nativePullFrame L a a' f ha (restrictPullbackIso a s b h e ≪≫ v) =
      restrictPullbackIso a' s b' (by rw [← ha, Category.assoc, h, hb]) e ≪≫
        nativePullFrame M b b' f hb v := by
  apply Iso.ext
  simp only [nativePullFrame_hom_triangle, Iso.trans_hom, Functor.map_comp, Category.assoc]
  rw [restrictPullbackIso_map_hom a s b h e f a' ha b' hb]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- A frame is determined by its normalized restriction along a map that
is injective on global scalars. -/
theorem frame_eq_of_nativePullFrame_eq {X Y Z : Scheme.{u}} (L : LineBundle X)
    (p : Y ⟶ X) (q : Z ⟶ X) (f : Z ⟶ Y) (w : f ≫ p = q)
    (hf : Function.Injective f.appTop)
    (v v' : (Scheme.Modules.pullback p).obj L.val ≅ SheafOfModules.unit Y.ringCatSheaf)
    (h : nativePullFrame L p q f w v = nativePullFrame L p q f w v') : v = v' := by
  apply lineBundleIso_eq_of_pullbackMap_eq f hf
    ((Scheme.Modules.pullback f).mapIso v ≪≫ pullbackUnitIso f)
    (L := pullbackLineBundle p L) (M := UnitPower.unitLineBundle Y) v v'
  have hh := congrArg Iso.hom h
  rw [nativePullFrame_hom_triangle, nativePullFrame_hom_triangle,
    cancel_epi, cancel_mono] at hh
  exact hh

private theorem pullbackCongr_symm_inv_app {S X : Scheme.{u}} {a b : S ⟶ X}
    (h : a = b) (M : X.Modules) :
    (pullbackCongr h).hom.app M = (pullbackCongr h.symm).inv.app M := by
  subst b
  rfl

private theorem nativePullFrame_triangle {X Y Z : Scheme.{u}} (L : LineBundle X)
    (p : Y ⟶ X) (q : Z ⟶ X) (f : Z ⟶ Y) (w : f ≫ p = q)
    (v : (Scheme.Modules.pullback p).obj L.val ≅ SheafOfModules.unit Y.ringCatSheaf) :
    nativePullFrame L p q f w v =
      ((pullbackTriangleIso f p q w).app L.val).symm ≪≫
        (Scheme.Modules.pullback f).mapIso v ≪≫ pullbackUnitIso f :=
  Iso.ext (nativePullFrame_hom_triangle L p q f w v)

private theorem symm_trans_cancel {C : Type*} [Category* C] {A B D : C}
    (e : A ≅ B) (u : B ≅ D) : e.symm ≪≫ (e ≪≫ u) = u := by
  rw [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]

set_option backward.isDefEq.respectTransparency false in
private theorem origin_frame_triangle {X U V W : Scheme.{u}} (L : LineBundle X)
    (s : V ⟶ W) (F : W ⟶ X) (t : V ⟶ U) (g : U ⟶ X) (w : s ≫ F = t ≫ g)
    (v : (Scheme.Modules.pullback g).obj L.val ≅ SheafOfModules.unit U.ringCatSheaf) :
    (pullbackTriangleIso s F (s ≫ F) rfl).app L.val ≪≫
      nativePullFrame L g (s ≫ F) t w.symm v =
    (pullbackComp s F).app L.val ≪≫ (pullbackCongr w).app L.val ≪≫
      ((pullbackComp t g).app L.val).symm ≪≫
      (Scheme.Modules.pullback t).mapIso v ≪≫ pullbackUnitIso t := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Functor.mapIso_hom,
    nativePullFrame_hom_triangle, pullbackTriangleIso_inv_app,
    pullbackTriangleIso_rfl_hom_app, Category.assoc]
  rw [pullbackCongr_symm_inv_app w L.val]

namespace RigidifiedPair

variable {S X : Scheme.{u}} {p : X ⟶ S} {o : S ⟶ X} {ho : o ≫ p = 𝟙 S}
  {T T' : Over S}

set_option backward.isDefEq.respectTransparency false in
/-- The original pulled-back rigidification in its triangle and frame form. -/
theorem map_rigidification_triangle (f : T' ⟶ T) (Q : RigidifiedPair p o ho T)
    (z : T'.left ⟶ pullback p T.hom)
    (hz : originSection p o ho T' ≫ (familyScheme p).map f = z) :
    (map f Q).rigidification =
      (pullbackTriangleIso (originSection p o ho T') ((familyScheme p).map f) z hz).app
        Q.bundle.val ≪≫
      nativePullFrame Q.bundle (originSection p o ho T) z f.left
        ((originSection_comp_familyScheme_map f).symm.trans hz) Q.rigidification := by
  subst z
  exact (origin_frame_triangle Q.bundle (originSection p o ho T') ((familyScheme p).map f)
    f.left (originSection p o ho T) (originSection_comp_familyScheme_map f)
    Q.rigidification).symm

set_option backward.isDefEq.respectTransparency false in
/-- The frame from an actual rigidified trivialization on a parameter
restriction agrees at the source origin with the restricted original frame. -/
theorem mapToTrivial_originFrame (f : T' ⟶ T) (Q : RigidifiedPair p o ho T)
    (e : Iso (map f Q) (trivialRigidifiedPair p o ho T')) :
    nativePullFrame Q.bundle ((familyScheme p).map f)
        (originSection p o ho T' ≫ (familyScheme p).map f) (originSection p o ho T') rfl
        (e.iso ≪≫ freeUnitIso (pullback p T'.hom)) =
      nativePullFrame Q.bundle (originSection p o ho T)
        (originSection p o ho T' ≫ (familyScheme p).map f) f.left
        (originSection_comp_familyScheme_map (p := p) (o := o) (ho := ho) f).symm
        Q.rigidification := by
  let F := (familyScheme p).map f
  let s := originSection p o ho T'
  let v := e.iso ≪≫ freeUnitIso (pullback p T'.hom)
  let c := (pullbackTriangleIso s F (s ≫ F) rfl).app Q.bundle.val
  have he : (Scheme.Modules.pullback s).mapIso v ≪≫ pullbackUnitIso s =
      (map f Q).rigidification := by
    apply CategoryTheory.Iso.ext
    simpa only [s, v, trivialRigidifiedPair, freeUnitIso, CategoryTheory.Iso.trans_hom,
      CategoryTheory.Functor.map_comp, CategoryTheory.Functor.mapIso_hom, Category.assoc]
      using e.comm
  have h0 := nativePullFrame_triangle Q.bundle F (s ≫ F) s rfl v
  have h1 := he.trans (map_rigidification_triangle f Q (s ≫ F) rfl)
  exact h0.trans ((congrArg (fun u => c.symm ≪≫ u) h1).trans (symm_trans_cancel c _))

end RigidifiedPair

private theorem inversePasting {C : Type*} [Category* C] {W X Y Z V : C}
    (p : W ≅ X) (b : W ≅ Y) (d : Y ≅ Z) (c : X ≅ V) (a : Z ≅ V)
    (h : p.symm ≪≫ b ≪≫ d = c ≪≫ a.symm) :
    b.symm ≪≫ p = d ≪≫ a ≪≫ c.symm := by
  simpa only [Iso.trans_symm, Iso.symm_symm_eq, ← Iso.trans_assoc, Iso.self_symm_id,
    Iso.refl_trans] using congrArg (fun e => d ≪≫ e.symm) h

set_option backward.isDefEq.respectTransparency false in
/-- The actual restriction of a tensor-powered isomorphism through a triangle. -/
theorem restrictPullbackIso_power {X Y Z : Scheme.{u}} (a : Y ⟶ X) (s : X ⟶ Z)
    (b : Y ⟶ Z) (w : a ≫ s = b) (L : LineBundle X) (M : LineBundle Z)
    (e : L.val ≅ (Scheme.Modules.pullback s).obj M.val) (n : ℕ) :
    restrictPullbackIso a s b w
        (TrivializedPower.powerIso X (L := L) (M := pullbackLineBundle s M) e n ≪≫
          (pullbackPowerIso s M n).symm) =
      pullbackPowerIso a L n ≪≫
        TrivializedPower.powerIso Y (L := pullbackLineBundle a L) (M := pullbackLineBundle b M)
          (restrictPullbackIso a s b w e) n ≪≫ (pullbackPowerIso b M n).symm := by
  subst b
  let c := (pullbackComp a s).app M.val
  let d := (pullbackComp a s).app (tensorPowerLineBundle Z M n).val
  let i := pullbackPowerIso a (pullbackLineBundle s M) n
  let j := (Scheme.Modules.pullback a).mapIso (pullbackPowerIso s M n)
  let k := pullbackPowerIso (a ≫ s) M n
  let r := TrivializedPower.powerIso Y (L := pullbackLineBundle a (pullbackLineBundle s M))
    (M := pullbackLineBundle (a ≫ s) M) c n
  have h : d.symm ≪≫ j ≪≫ i = k ≪≫ r.symm := by
    apply CategoryTheory.Iso.ext
    have hs := congrArg CategoryTheory.Iso.hom (UnitPower.powerIso_symm Y
      (L := pullbackLineBundle a (pullbackLineBundle s M))
      (M := pullbackLineBundle (a ≫ s) M) c n)
    have hc := PowerPullbackNaturality.pullbackPowerIso_comp a s M n
    simp only [d, j, i, k, r, CategoryTheory.Iso.trans_hom, CategoryTheory.Iso.symm_hom,
      CategoryTheory.Functor.mapIso_hom]
    exact hc.trans (congrArg (fun t => k.hom ≫ t) hs)
  have hr := inversePasting d j i k r h
  have hp : (pullbackTriangleIso a s (a ≫ s) rfl).app M.val = c :=
    CategoryTheory.Iso.ext (pullbackTriangleIso_rfl_hom_app a s M.val)
  have hpp : (pullbackTriangleIso a s (a ≫ s) rfl).app (tensorPowerLineBundle Z M n).val = d :=
    CategoryTheory.Iso.ext (pullbackTriangleIso_rfl_hom_app a s (tensorPowerLineBundle Z M n).val)
  let F := Scheme.Modules.pullback a
  let p := pullbackPowerIso a L n
  let E := TrivializedPower.powerIso X (L := L) (M := pullbackLineBundle s M) e n
  let E' := TrivializedPower.powerIso Y (L := pullbackLineBundle a L)
    (M := pullbackLineBundle a (pullbackLineBundle s M)) (F.mapIso e) n
  have hn : F.mapIso E ≪≫ i = p ≪≫ E' :=
    PowerPullbackNaturality.pullbackPowerIso_naturality a
      (L := L) (M := pullbackLineBundle s M) e n
  have ht := UnitPower.powerIso_trans Y (L := pullbackLineBundle a L)
    (M := pullbackLineBundle a (pullbackLineBundle s M)) (N := pullbackLineBundle (a ≫ s) M)
    (F.mapIso e) c n
  have hL : restrictPullbackIso a s (a ≫ s) rfl (E ≪≫ (pullbackPowerIso s M n).symm) =
      (F.mapIso E ≪≫ j.symm) ≪≫ d :=
    congrArg₂ (fun x y => x ≪≫ y)
      ((F.mapIso_trans E (pullbackPowerIso s M n).symm).trans
        (congrArg (fun y => F.mapIso E ≪≫ y) (F.mapIso_symm (pullbackPowerIso s M n)))) hpp
  have hP : restrictPullbackIso a s (a ≫ s) rfl e = F.mapIso e ≪≫ c :=
    congrArg (fun x => F.mapIso e ≪≫ x) hp
  have hR := congrArg (fun x => p ≪≫ x ≪≫ k.symm)
    ((congrArg (fun x => TrivializedPower.powerIso Y (L := pullbackLineBundle a L)
      (M := pullbackLineBundle (a ≫ s) M) x n) hP).trans ht)
  calc
    _ = (F.mapIso E ≪≫ j.symm) ≪≫ d := hL
    _ = F.mapIso E ≪≫ i ≪≫ r ≪≫ k.symm :=
      (CategoryTheory.Iso.trans_assoc _ _ _).trans (congrArg (fun x => F.mapIso E ≪≫ x) hr)
    _ = p ≪≫ (E' ≪≫ r) ≪≫ k.symm := by
      simpa only [CategoryTheory.Iso.trans_assoc] using congrArg (fun x => x ≪≫ r ≪≫ k.symm) hn
    _ = _ := hR.symm

set_option backward.isDefEq.respectTransparency false in
/-- The conjugated comparison on a test fixed by the swap, when its powered
swap restriction is the identity. All transports are the original triangles. -/
theorem restrictPullbackIso_transpose_fixed {X Y : Scheme.{u}} (s m t : X ⟶ X)
    (w : s ≫ t = m ≫ s) {L N : X.Modules}
    (e : L ≅ (Scheme.Modules.pullback s).obj L)
    (b : N ≅ (Scheme.Modules.pullback t).obj L)
    (a : N ≅ (Scheme.Modules.pullback s).obj N)
    (r : Y ⟶ X) (hr : r ≫ s = r) (u v : Y ⟶ X) (hu : r ≫ m = u) (hv : r ≫ t = v)
    (ha : restrictPullbackIso r s r hr a = Iso.refl _) :
    restrictPullbackIso r m u hu
        (a ≪≫ restrictPullbackIso s t (m ≫ s) w b ≪≫ ((pullbackComp m s).app L).symm ≪≫
          (Scheme.Modules.pullback m).mapIso e.symm) =
      restrictPullbackIso r t v hv b ≪≫
        (restrictPullbackIso u s v (by rw [← hu, Category.assoc, ← w,
          ← Category.assoc, hr, hv]) e).symm := by
  have hrv : r ≫ (m ≫ s) = v := by rw [← w, ← Category.assoc, hr, hv]
  have huv : u ≫ s = v := by rw [← hu, Category.assoc, hrv]
  have ha' := congrArg CategoryTheory.Iso.hom ha
  change (Scheme.Modules.pullback r).map a.hom ≫ (pullbackTriangleIso r s r hr).hom.app N =
    𝟙 _ at ha'
  have hb := restrictPullbackIso_map_hom s t (m ≫ s) w b r r hr v hrv
  have he := (pullbackTriangleIso r m u hu).hom.naturality e.inv
  simp only [Functor.comp_map] at he
  let c0 := (pullbackTriangleIso m s (m ≫ s) rfl).app L
  let c1 := (pullbackTriangleIso r m u hu).app ((Scheme.Modules.pullback s).obj L)
  let c2 := (pullbackTriangleIso u s v huv).app L
  let c3 := (pullbackTriangleIso r (m ≫ s) v hrv).app L
  have hc : (Scheme.Modules.pullback r).mapIso c0 = c1 ≪≫ c2 ≪≫ c3.symm := by
    apply CategoryTheory.Iso.ext
    exact pullback_map_pullbackTriangleIso_hom_app r m s hu rfl hrv L
  have hi : (Scheme.Modules.pullback r).map ((pullbackComp m s).inv.app L) =
      c3.hom ≫ c2.inv ≫ c1.inv := by
    have h := congrArg CategoryTheory.Iso.inv hc
    simpa only [c0, pullbackTriangleIso_rfl_inv_app, Iso.app_inv, Functor.mapIso_inv,
      Iso.trans_inv, Iso.symm_inv, Category.assoc] using h
  apply CategoryTheory.Iso.ext
  change (Scheme.Modules.pullback r).map
      (a ≪≫ restrictPullbackIso s t (m ≫ s) w b ≪≫ ((pullbackComp m s).app L).symm ≪≫
        (Scheme.Modules.pullback m).mapIso e.symm).hom ≫
      (pullbackTriangleIso r m u hu).hom.app L = _
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hb]
  simp only [Category.assoc]
  rw [reassoc_of% ha', hi]
  simp only [Category.assoc]
  rw [he]
  let q := (restrictPullbackIso r t v hv b).hom
  change q ≫ c3.inv ≫ c3.hom ≫ c2.inv ≫ c1.inv ≫ c1.hom ≫
      (Scheme.Modules.pullback u).map e.inv =
    q ≫ c2.inv ≫ (Scheme.Modules.pullback u).map e.inv
  rw [Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The two power frames along an axis agree once their actual restrictions
agree at a point that detects global scalars. -/
theorem powerFrame_axis_of_origin {X Y Z : Scheme.{u}} (L : LineBundle X)
    (m : X ⟶ X) (a b : Y ⟶ X) (h : a ≫ m = b) (o : Z ⟶ Y)
    (z : Z ⟶ X) (ha : o ≫ a = z) (hb : o ≫ b = z) (hz : z ≫ m = z)
    (ho : Function.Injective o.appTop) (n : ℕ)
    (u : (Scheme.Modules.pullback a).obj L.val ≅ SheafOfModules.unit Y.ringCatSheaf)
    (v : (Scheme.Modules.pullback b).obj L.val ≅ SheafOfModules.unit Y.ringCatSheaf)
    (e : (tensorPowerLineBundle X L n).val ≅ (Scheme.Modules.pullback m).obj L.val)
    (huv : nativePullFrame L b z o hb v = nativePullFrame L a z o ha u)
    (he : restrictPullbackIso z m z hz e ≪≫
        nativePullFrame L a z o ha u =
      PowerDescent.powerFrame L z (nativePullFrame L a z o ha u) n) :
    restrictPullbackIso a m b h e ≪≫ v = PowerDescent.powerFrame L a u n := by
  apply frame_eq_of_nativePullFrame_eq (tensorPowerLineBundle X L n) a z o ha ho
  have h1 := nativePullFrame_restrictPullbackIso a m b h (tensorPowerLineBundle X L n)
    L e v o z ha z hb
  have h2 := congrArg (fun w =>
    restrictPullbackIso z m z hz e ≪≫ w) huv
  have h3 := PowerDescent.powerFrame_nativePullFrame L a z o ha u n
  exact h1.trans (h2.trans (he.trans h3.symm))

end AlgebraicGeometry.Scheme.RelativePicard
