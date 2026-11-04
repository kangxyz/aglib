/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.KernelIso
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.AmpleKernel
public import Aglib.AlgebraicGeometry.Group.MultiplicationKernel.Functoriality
public import Aglib.AlgebraicGeometry.Picard.LinearSystem.Basic
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.PoincareSymmetry

/-!
# The diagonal of the original Poincare kernel character

The ratio of the two normalized powers gives the original kernel frame for a
polarization point. Its restrictions at the source origin and the diagonal
torsion point agree, so the original deck multiplier is trivial there.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.OverField Scheme.Group
open Scheme.Modules Scheme.Modules.Invertible
open Scheme.Modules.Invertible.PowerPullback
open Scheme.Modules.Invertible.TrivializedPowerTorsor

universe u

attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false in
private theorem restrictPullbackIso_map_inv {X Y Z T : Scheme.{u}} (a : Y ⟶ X) (s : X ⟶ Z)
    (b : Y ⟶ Z) (h : a ≫ s = b) {L : X.Modules} {M : Z.Modules}
    (e : L ≅ (Scheme.Modules.pullback s).obj M) (f : T ⟶ Y) (a' : T ⟶ X) (ha : f ≫ a = a')
    (b' : T ⟶ Z) (hb : f ≫ b = b') :
    (Scheme.Modules.pullback f).map (restrictPullbackIso a s b h e).inv =
      (pullbackTriangleIso f b b' hb).hom.app M ≫
        (restrictPullbackIso a' s b' (by rw [← ha, Category.assoc, h, hb]) e).inv ≫
        (pullbackTriangleIso f a a' ha).inv.app L := by
  have he : (Scheme.Modules.pullback f).mapIso (restrictPullbackIso a s b h e) =
      (pullbackTriangleIso f a a' ha).app L ≪≫
        restrictPullbackIso a' s b' (by rw [← ha, Category.assoc, h, hb]) e ≪≫
        ((pullbackTriangleIso f b b' hb).app M).symm :=
    CategoryTheory.Iso.ext (restrictPullbackIso_map_hom a s b h e f a' ha b' hb)
  simpa only [Functor.mapIso_inv, CategoryTheory.Iso.trans_inv, CategoryTheory.Iso.app_inv,
    CategoryTheory.Iso.symm_inv, CategoryTheory.Iso.app_hom, Category.assoc] using
      congrArg CategoryTheory.Iso.inv he

set_option backward.isDefEq.respectTransparency false in
private theorem nativePullFrame_hom_triangle {X Y Z : Scheme.{u}} (L : LineBundle X)
    (p : Y ⟶ X) (q : Z ⟶ X) (f : Z ⟶ Y) (w : f ≫ p = q)
    (v : (Scheme.Modules.pullback p).obj L.val ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (nativePullFrame L p q f w v).hom =
      (pullbackTriangleIso f p q w).inv.app L.val ≫ (Scheme.Modules.pullback f).map v.hom ≫
        (pullbackUnitIso f).hom := by
  simp only [nativePullFrame, pullbackTriangleIso_inv_app, CategoryTheory.Iso.trans_hom,
    CategoryTheory.Iso.symm_hom, CategoryTheory.Iso.app_inv, Functor.mapIso_hom, Category.assoc]

private theorem nativePullFrame_congr_map {X Y Z : Scheme.{u}} (M : LineBundle X)
    (p : Y ⟶ X) (q : Z ⟶ X) {f g : Z ⟶ Y} (h : f = g) (hf : f ≫ p = q)
    (hg : g ≫ p = q)
    (v : (Scheme.Modules.pullback p).obj M.val ≅ SheafOfModules.unit Y.ringCatSheaf) :
    nativePullFrame M p q f hf v = nativePullFrame M p q g hg v := by
  subst g
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The ratio of two actual pullback isomorphisms followed by an axis frame. -/
def ratioPullbackFrame {X H Y : Scheme.{u}} (L : LineBundle X) (r : H ⟶ X) (p : H ⟶ H)
    (m₁ m₂ : X ⟶ X) (hp : p ≫ r = r ≫ m₁) (j : H ⟶ Y) (k : Y ⟶ X)
    (hj : j ≫ k = r ≫ m₂) {N : X.Modules} (a : N ≅ (Scheme.Modules.pullback m₁).obj L.val)
    (b : N ≅ (Scheme.Modules.pullback m₂).obj L.val)
    (v : (Scheme.Modules.pullback k).obj L.val ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.pullback p).obj (pullbackLineBundle r L).val ≅
      SheafOfModules.unit H.ringCatSheaf :=
  (pullbackTriangleIso p r (r ≫ m₁) hp).app L.val ≪≫
    (restrictPullbackIso r m₁ (r ≫ m₁) rfl a).symm ≪≫
      restrictPullbackIso r m₂ (r ≫ m₂) rfl b ≪≫ nativePullFrame L k (r ≫ m₂) j hj v

private theorem ratio_eq_frame {C : Type*} [Category* C] {N U V O : C}
    (a : N ≅ U) (b : N ≅ V) (u : U ≅ O) (v : V ≅ O) (h : a ≪≫ u = b ≪≫ v) :
    a.symm ≪≫ b ≪≫ v = u := by
  rw [← h, ← CategoryTheory.Iso.trans_assoc, CategoryTheory.Iso.symm_self_id,
    CategoryTheory.Iso.refl_trans]

set_option backward.isDefEq.respectTransparency false in
private theorem ratioPullbackFrame_pull {X H Y V : Scheme.{u}} (L : LineBundle X) (r : H ⟶ X)
    (p : H ⟶ H) (m₁ m₂ : X ⟶ X) (hp : p ≫ r = r ≫ m₁) (j : H ⟶ Y) (k : Y ⟶ X)
    (hj : j ≫ k = r ≫ m₂) {N : X.Modules} (a : N ≅ (Scheme.Modules.pullback m₁).obj L.val)
    (b : N ≅ (Scheme.Modules.pullback m₂).obj L.val)
    (v : (Scheme.Modules.pullback k).obj L.val ≅ SheafOfModules.unit Y.ringCatSheaf)
    (g q : V ⟶ H) (h : g ≫ p = q) (x u w : V ⟶ X) (hx : g ≫ r = x) (hu : q ≫ r = u)
    (hw : g ≫ (r ≫ m₂) = w) (z : V ⟶ Y) (hz : g ≫ j = z)
    (ou : (Scheme.Modules.pullback u).obj L.val ≅ SheafOfModules.unit V.ringCatSheaf)
    (he : restrictPullbackIso x m₁ u
        (by rw [← hx, Category.assoc, ← hp, ← Category.assoc, h, hu]) a ≪≫ ou =
      restrictPullbackIso x m₂ w (by rw [← hx, Category.assoc, hw]) b ≪≫
        nativePullFrame L k w z (by rw [← hz, Category.assoc, hj, hw]) v) :
    nativePullFrame (pullbackLineBundle r L) p q g h
        (ratioPullbackFrame L r p m₁ m₂ hp j k hj a b v) =
      (pullbackTriangleIso q r u hu).app L.val ≪≫ ou := by
  have hc : g ≫ (r ≫ m₁) = u := by rw [← hp, ← Category.assoc, h, hu]
  have hx₁ : x ≫ m₁ = u := by rw [← hx, Category.assoc, hc]
  have hx₂ : x ≫ m₂ = w := by rw [← hx, Category.assoc, hw]
  have hz' : z ≫ k = w := by rw [← hz, Category.assoc, hj, hw]
  let a' := restrictPullbackIso x m₁ u hx₁ a
  let b' := restrictPullbackIso x m₂ w hx₂ b
  let v' := nativePullFrame L k w z hz' v
  have ht := pullback_map_pullbackTriangleIso_hom_app g p r h hp hc L.val
  have ha := restrictPullbackIso_map_inv r m₁ (r ≫ m₁) rfl a g x hx u hc
  have hb := restrictPullbackIso_map_hom r m₂ (r ≫ m₂) rfl b g x hx w hw
  have hf := congrArg CategoryTheory.Iso.hom
    ((PowerBaseChange.nativePullFrame_comp L k (r ≫ m₂) w j g hj hw v).trans
      (nativePullFrame_congr_map L k w hz _ hz' v))
  rw [nativePullFrame_hom_triangle L (r ≫ m₂) w g hw] at hf
  have hcancel := congrArg CategoryTheory.Iso.hom (ratio_eq_frame a' b' ou v' he)
  change (a'.symm ≪≫ b' ≪≫ v').hom = ou.hom at hcancel
  simp only [CategoryTheory.Iso.trans_hom, CategoryTheory.Iso.symm_hom] at hcancel
  apply CategoryTheory.Iso.ext
  rw [nativePullFrame_hom_triangle]
  simp only [ratioPullbackFrame, CategoryTheory.Iso.trans_hom, CategoryTheory.Iso.symm_hom,
    CategoryTheory.Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [ht, ha, hb]
  simp only [Category.assoc, CategoryTheory.Iso.inv_hom_id_app_assoc]
  rw [hf]
  change (pullbackTriangleIso g p q h).inv.app ((Scheme.Modules.pullback r).obj L.val) ≫
    (pullbackTriangleIso g p q h).hom.app ((Scheme.Modules.pullback r).obj L.val) ≫
    (pullbackTriangleIso q r u hu).hom.app L.val ≫ a'.inv ≫ b'.hom ≫ v'.hom =
      (pullbackTriangleIso q r u hu).hom.app L.val ≫ ou.hom
  rw [CategoryTheory.Iso.inv_hom_id_app_assoc, hcancel]

section Polarized

variable {k : Type u} [Field k] (A : Grp (FScheme k))
  [IsProper A.X.hom] [GeometricallyIntegral A.X.hom] [IsCommMonObj A.X]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  (L : LineBundle A.X.left) (n : ℕ) {T : FScheme k} (x : T ⟶ A.X)

local notation "q" => MultiplicationKernel.multiplicationHom A n
local notation "m" => ((𝟙 A.X) ^ n)
local notation "F" => LinearSystem.familyMap A.X.hom x
local notation "p" => familyMapOfHom (Mon.Hom.hom (InducedCategory.Hom.hom q)) T
local notation "m₁" => familyMapOfHom m A.X
local notation "m₂" => LinearSystem.familyMap A.X.hom m
local notation "j" => pullback.fst A.X.hom T.hom
local notation "a₁" => polarizedSourceAxis A.X
local notation "a₂" => polarizedParameterAxis A.X
local notation "B" => polarizedPoincarePair A.X P R L
local notation "s" => originSection A.X.hom (Over.Hom.left η[A.X]) (Over.w η[A.X]) T
local notation "d" => Over.Hom.left (lift x (𝟙 T))

omit [IsProper A.X.hom] [GeometricallyIntegral A.X.hom] in
theorem multiplicationHom_underlying_power : (q).hom.hom = m := by
  rw [MultiplicationKernel.multiplicationHom_hom, MultiplicationKernel.multiplication]

omit [IsProper A.X.hom] [GeometricallyIntegral A.X.hom] in
theorem polarizedKernel_first_square : p ≫ F = F ≫ m₁ := by
  rw [← multiplicationHom_underlying_power A n]
  exact (familyMapOfHom_naturality (q).hom.hom x).symm

omit [IsProper A.X.hom] [GeometricallyIntegral A.X.hom] in
set_option backward.isDefEq.respectTransparency false in
theorem polarizedKernel_parameter_square (hx : x ≫ (q).hom.hom = 1) :
    j ≫ a₂ = F ≫ m₂ := by
  have h : x ≫ m = 1 := by
    rw [← multiplicationHom_underlying_power A n]
    exact hx
  rw [polarizedParameterAxis_eq_lift, ← LinearSystem.familyMap_comp, h]
  change ((fst A.X T) ≫ lift (𝟙 A.X) (1 : A.X ⟶ A.X)).left =
    (A.X ◁ (1 : T ⟶ A.X)).left
  apply congrArg (fun f : A.X ⊗ T ⟶ A.X ⊗ A.X => f.left)
  apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.comp_one]

set_option backward.isDefEq.respectTransparency false in
/-- The ratio on the original multiplication pullback of the polarized pair. -/
def polarizedKernelRatioFrame (hx : x ≫ (q).hom.hom = 1) :
    (Scheme.Modules.pullback p).obj (RigidifiedPair.map x B).bundle.val ≅
      SheafOfModules.unit (pullback A.X.hom T.hom).ringCatSheaf :=
  let M : LineBundle (pullback A.X.hom A.X.hom) := (B).bundle
  let N := tensorPowerLineBundle (pullback A.X.hom A.X.hom) M n
  let a : N.val ≅ (Scheme.Modules.pullback m₁).obj M.val :=
    polarizedFirstPowerIso A.X P R L n
  let b : N.val ≅ (Scheme.Modules.pullback m₂).obj M.val :=
    (polarizedSecondPowerIso A.X P R L n).iso
  ratioPullbackFrame M F p m₁ m₂ (polarizedKernel_first_square A n x) j a₂
    (polarizedKernel_parameter_square A n x hx) a b (polarizedParameterFrame A.X P R L)

omit [IsProper A.X.hom] [GeometricallyIntegral A.X.hom] in
/-- The original multiplication family preserves the source origin. -/
theorem polarizedKernel_origin_mul : s ≫ p = s :=
  originSection_comp_familyMapOfHom η[A.X] η[A.X] (q).hom.hom (IsMonHom.one_hom _) T

omit [IsProper A.X.hom] [GeometricallyIntegral A.X.hom] [IsCommMonObj A.X] in
private theorem polarizedKernel_origin_family : s ≫ F = x.left ≫ a₁ :=
  RigidifiedPair.originSection_comp_familyScheme_map
    («p» := A.X.hom) (o := η[A.X].left) (ho := Over.w η[A.X]) x

omit [IsProper A.X.hom] [GeometricallyIntegral A.X.hom] in
/-- Multiplication sends the lifted torsion point to the source origin. -/
theorem polarizedKernel_diagonal_mul (hx : x ≫ (q).hom.hom = 1) : d ≫ p = s := by
  rw [lift_comp_familyMap q T x (𝟙 T), hx, originSection_eq_unit_axis]

omit [IsProper A.X.hom] [GeometricallyIntegral A.X.hom] [IsCommMonObj A.X] in
set_option backward.isDefEq.respectTransparency false in
private theorem polarizedKernel_diagonal_family : d ≫ F = x.left ≫ polarizedDiagonal A.X := by
  change (lift x (𝟙 T) ≫ (A.X ◁ x)).left =
    (x ≫ lift (𝟙 A.X) (𝟙 A.X)).left
  apply congrArg (fun f : T ⟶ A.X ⊗ A.X => f.left)
  apply CartesianMonoidalCategory.hom_ext <;> simp

omit [IsProper A.X.hom] [GeometricallyIntegral A.X.hom] [IsCommMonObj A.X] in
private theorem polarizedKernel_diagonal_fst : d ≫ j = x.left := by
  rw [Over.lift_left, pullback.lift_fst]

omit [IsProper A.X.hom] [GeometricallyIntegral A.X.hom] in
private theorem polarizedKernel_origin_fst :
    s ≫ j = (1 : T ⟶ A.X).left := by
  rw [originSection_eq_unit_axis, Over.lift_left, pullback.lift_fst]

omit [IsSeparated P.obj.hom] in
set_option backward.isDefEq.respectTransparency false in
private theorem polarizedKernel_axis_frames (hx : x ≫ (q).hom.hom = 1) :
    nativePullFrame (B).bundle a₁
        ((1 : T ⟶ A.X).left ≫ a₂) (x.left ≫ (m).left)
        (by
          have h := congrArg (fun f : T ⟶ A.X => f.left)
            ((multiplicationHom_underlying_power A n ▸ hx) : x ≫ m = 1)
          rw [Over.comp_left] at h
          have hη : (1 : T ⟶ A.X).left = T.hom ≫ η[A.X].left := rfl
          rw [h, hη]
          simp only [Category.assoc, origin_comp_polarizedParameterAxis, polarizedOrigin])
        (B).rigidification =
      nativePullFrame (B).bundle a₂ ((1 : T ⟶ A.X).left ≫ a₂) (1 : T ⟶ A.X).left
        rfl (polarizedParameterFrame A.X P R L) := by
  have h : x ≫ m = 1 := by
    rw [← multiplicationHom_underlying_power A n]
    exact hx
  have h' : x.left ≫ (m).left = (1 : T ⟶ A.X).left :=
    congrArg (fun f : T ⟶ A.X => f.left) h
  have hη : (1 : T ⟶ A.X).left = T.hom ≫ η[A.X].left := rfl
  let z := polarizedOrigin A.X
  let w := (1 : T ⟶ A.X).left ≫ a₂
  have hz : T.hom ≫ z = w := by
    change T.hom ≫ z = (1 : T ⟶ A.X).left ≫ a₂
    rw [hη, Category.assoc, origin_comp_polarizedParameterAxis]
  have ha := PowerBaseChange.nativePullFrame_comp (B).bundle a₁ z w η[A.X].left T.hom rfl hz
    (B).rigidification
  have hb := PowerBaseChange.nativePullFrame_comp (B).bundle a₂ z w η[A.X].left T.hom
    (origin_comp_polarizedParameterAxis A.X) hz (polarizedParameterFrame A.X P R L)
  have hc := congrArg (nativePullFrame (B).bundle z w T.hom hz)
    (polarizedParameterFrame_origin A.X P R L)
  exact (nativePullFrame_congr_map (B).bundle a₁ w (h'.trans hη) _ _
      (B).rigidification).trans
    (ha.symm.trans (hc.symm.trans (hb.trans
      (nativePullFrame_congr_map (B).bundle a₂ w hη.symm _ _
        (polarizedParameterFrame A.X P R L)))))

set_option backward.isDefEq.respectTransparency false in
private theorem polarizedKernel_axis_trivializations (hx : x ≫ (q).hom.hom = 1) :
    let u := x.left ≫ a₁
    let w := (1 : T ⟶ A.X).left ≫ a₂
    restrictPullbackIso u m₁ u (by rw [Category.assoc, sourceAxis_firstPower A.X n])
        (polarizedFirstPowerIso A.X P R L n) ≪≫
      nativePullFrame (B).bundle a₁ u x.left rfl (B).rigidification =
    restrictPullbackIso u m₂ w (by
        change (x.left ≫ a₁) ≫ m₂ = (1 : T ⟶ A.X).left ≫ a₂
        rw [← polarizedKernel_origin_family A x, Category.assoc,
          ← polarizedKernel_parameter_square A n x hx, ← Category.assoc,
          polarizedKernel_origin_fst A (T := T)])
        (polarizedSecondPowerIso A.X P R L n).iso ≪≫
      nativePullFrame (B).bundle a₂ w (1 : T ⟶ A.X).left rfl
        (polarizedParameterFrame A.X P R L) := by
  let u := x.left ≫ a₁
  let w := (1 : T ⟶ A.X).left ≫ a₂
  have hw : x.left ≫ (a₁ ≫ m₂) = w := by
    rw [← Category.assoc, ← polarizedKernel_origin_family A x, Category.assoc,
      ← polarizedKernel_parameter_square A n x hx, ← Category.assoc, polarizedKernel_origin_fst A]
  let W := tensorPowerLineBundle (pullback A.X.hom A.X.hom) (B).bundle n
  let a := polarizedFirstPowerIso A.X P R L n
  let b := (polarizedSecondPowerIso A.X P R L n).iso
  let o := (B).rigidification
  let v := polarizedParameterFrame A.X P R L
  let o' := nativePullFrame (B).bundle a₁ (a₁ ≫ m₂) (m).left
    (sourceAxis_secondPower A.X n).symm o
  let f := PowerDescent.powerFrame (B).bundle a₁ o n
  have ha := nativePullFrame_restrictPullbackIso a₁ m₁ a₁ (sourceAxis_firstPower A.X n)
    W (B).bundle a o x.left u rfl u rfl
  have hb := nativePullFrame_restrictPullbackIso a₁ m₂ (a₁ ≫ m₂) rfl W (B).bundle
    b o' x.left u rfl w hw
  have h₁ : restrictPullbackIso a₁ m₁ a₁ (sourceAxis_firstPower A.X n) a ≪≫ o = f :=
    polarizedFirstPowerIso_sourceAxis A.X P R L n
  have h₂ : restrictPullbackIso a₁ m₂ (a₁ ≫ m₂) rfl b ≪≫ o' = f :=
    polarizedSecondPowerIso_sourceAxis A.X P R L n
  rw [h₁] at ha
  rw [h₂] at hb
  have hc := PowerBaseChange.nativePullFrame_comp (B).bundle a₁ (a₁ ≫ m₂) w (m).left x.left
    (sourceAxis_secondPower A.X n).symm hw o
  have hd : nativePullFrame (B).bundle (a₁ ≫ m₂) w x.left hw o' =
      nativePullFrame (B).bundle a₂ w (1 : T ⟶ A.X).left rfl v :=
    hc.trans (polarizedKernel_axis_frames A P R L n x hx)
  rw [hd] at hb
  exact ha.symm.trans hb

set_option backward.isDefEq.respectTransparency false in
/-- At the origin the ratio has the original source rigidification. -/
theorem polarizedKernelRatioFrame_origin (hx : x ≫ (q).hom.hom = 1) :
    nativePullFrame (RigidifiedPair.map x B).bundle p s s
      (polarizedKernel_origin_mul A n) (polarizedKernelRatioFrame A P R L n x hx) =
      (RigidifiedPair.map x B).rigidification := by
  let u := x.left ≫ a₁
  let w := (1 : T ⟶ A.X).left ≫ a₂
  have hu : s ≫ F = u := polarizedKernel_origin_family A x
  have hw : s ≫ (F ≫ m₂) = w := by
    rw [← polarizedKernel_parameter_square A n x hx, ← Category.assoc,
      polarizedKernel_origin_fst A]
  let ou := nativePullFrame (B).bundle a₁ u x.left rfl (B).rigidification
  have axes := polarizedKernel_axis_trivializations A P R L n x hx
  have he := ratioPullbackFrame_pull (B).bundle F p m₁ m₂
    (polarizedKernel_first_square A n x) j a₂ (polarizedKernel_parameter_square A n x hx)
    (polarizedFirstPowerIso A.X P R L n) (polarizedSecondPowerIso A.X P R L n).iso
    (polarizedParameterFrame A.X P R L) s s (polarizedKernel_origin_mul A n) u u w hu hu hw
    (1 : T ⟶ A.X).left (polarizedKernel_origin_fst A) ou
    axes
  have hr := RigidifiedPair.map_rigidification_triangle x B u hu
  exact he.trans hr.symm

set_option backward.isDefEq.respectTransparency false in
/-- The same ratio restricts at the diagonal torsion point to that rigidification. -/
theorem polarizedKernelRatioFrame_diagonal (hx : x ≫ (q).hom.hom = 1) :
    nativePullFrame (RigidifiedPair.map x B).bundle p s d
      (polarizedKernel_diagonal_mul A n x hx) (polarizedKernelRatioFrame A P R L n x hx) =
      (RigidifiedPair.map x B).rigidification := by
  let u := x.left ≫ a₁
  let w := x.left ≫ a₂
  have hu : s ≫ F = u := polarizedKernel_origin_family A x
  have hw : d ≫ (F ≫ m₂) = w := by
    rw [← polarizedKernel_parameter_square A n x hx, ← Category.assoc,
      polarizedKernel_diagonal_fst A x]
  have h : x ≫ m = 1 := by
    rw [← multiplicationHom_underlying_power A n]
    exact hx
  let ou := nativePullFrame (B).bundle a₁ u x.left rfl (B).rigidification
  have he := ratioPullbackFrame_pull (B).bundle F p m₁ m₂
    (polarizedKernel_first_square A n x) j a₂ (polarizedKernel_parameter_square A n x hx)
    (polarizedFirstPowerIso A.X P R L n) (polarizedSecondPowerIso A.X P R L n).iso
    (polarizedParameterFrame A.X P R L) d s (polarizedKernel_diagonal_mul A n x hx)
    (x.left ≫ polarizedDiagonal A.X) u w (polarizedKernel_diagonal_family A x) hu hw
    x.left (polarizedKernel_diagonal_fst A x) ou
    (polarizedPower_diagonal_trivializations A.X P R L x n h)
  exact he.trans (RigidifiedPair.map_rigidification_triangle x B u hu).symm

set_option backward.isDefEq.respectTransparency false in
/-- A frame on the original source pullback normalized at the origin
gives a rigidified isomorphism to the original trivial pair. -/
def RigidifiedPair.sourcePullbackIsoOfFrame {S : Scheme.{u}} {X Y : Over S}
    (oX : 𝟙_ (Over S) ⟶ X) (oY : 𝟙_ (Over S) ⟶ Y) (f : X ⟶ Y)
    (hf : oX ≫ f = oY) {T : Over S}
    (Q : RigidifiedPair Y.hom oY.left (Over.w oY) T)
    (v : (Scheme.Modules.pullback (familyMapOfHom f T)).obj Q.bundle.val ≅
      SheafOfModules.unit (pullback X.hom T.hom).ringCatSheaf)
    (hv : nativePullFrame Q.bundle (familyMapOfHom f T)
      (originSection Y.hom oY.left (Over.w oY) T) (originSection X.hom oX.left (Over.w oX) T)
      (originSection_comp_familyMapOfHom oX oY f hf T) v = Q.rigidification) :
    RigidifiedPair.Iso (RigidifiedPair.sourcePullback oX oY f hf Q)
      (trivialRigidifiedPair X.hom oX.left (Over.w oX) T) where
  iso := v ≪≫ (freeUnitIso (pullback X.hom T.hom)).symm
  comm := by
    let fT := familyMapOfHom f T
    let oT := originSection X.hom oX.left (Over.w oX) T
    let t := originSection Y.hom oY.left (Over.w oY) T
    let c := pullbackTriangleIso oT fT t (originSection_comp_familyMapOfHom oX oY f hf T)
    let e := freeUnitIso (pullback X.hom T.hom)
    have h := congrArg CategoryTheory.Iso.hom hv
    rw [nativePullFrame_hom_triangle] at h
    change c.inv.app Q.bundle.val ≫ (Scheme.Modules.pullback oT).map v.hom ≫
      (pullbackUnitIso oT).hom = Q.rigidification.hom at h
    have hn : (Scheme.Modules.pullback oT).map v.hom ≫ (pullbackUnitIso oT).hom =
        c.hom.app Q.bundle.val ≫ Q.rigidification.hom := by
      have he := congrArg (fun g => c.hom.app Q.bundle.val ≫ g) h
      simpa only [Category.assoc, CategoryTheory.Iso.hom_inv_id_app_assoc] using he
    change (Scheme.Modules.pullback oT).map (v.hom ≫ e.inv) ≫
      (Scheme.Modules.pullback oT).map e.hom ≫ (pullbackUnitIso oT).hom =
      (pullbackComp oT fT).hom.app Q.bundle.val ≫
        (pullbackCongr (originSection_comp_familyMapOfHom oX oY f hf T)).hom.app Q.bundle.val ≫
          Q.rigidification.hom
    rw [CategoryTheory.Functor.map_comp, Category.assoc,
      ← (Scheme.Modules.pullback oT).map_comp_assoc e.inv e.hom, CategoryTheory.Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact hn

local notation "φ" => lineBundleClassMorphismIdentityComponent A.X P R (classOf A.X.left L)

set_option backward.isDefEq.respectTransparency false in
/-- The original normalized Poincare kernel frame is the ratio of the two
actual powers after the original parameter comparison. -/
theorem poincareKernelFrame_eq_polarizedKernelRatioFrame
    (hx : x ≫ (q).hom.hom = 1)
    (ht : (x ≫ φ) ≫ picardIdentityComponentPullback P R P R (q).hom.hom = 1) :
    poincareKernelFrame A A P R P R q (x ≫ φ) ht =
      (Scheme.Modules.pullback p).mapIso (poincarePullbackCompIso A.X P R x φ).iso ≪≫
        polarizedKernelRatioFrame A P R L n x hx := by
  let c := RigidifiedPair.Iso.sourcePullback η[A.X] η[A.X] (q).hom.hom
    (IsMonHom.one_hom _) (poincarePullbackCompIso A.X P R x φ)
  let v := polarizedKernelRatioFrame A P R L n x hx
  let e := freeUnitIso (pullback A.X.hom T.hom)
  let b := RigidifiedPair.sourcePullbackIsoOfFrame η[A.X] η[A.X] (q).hom.hom
    (IsMonHom.one_hom _) (RigidifiedPair.map x B) v
    (polarizedKernelRatioFrame_origin A P R L n x hx)
  have h := poincareKernelTrivialization_unique A A P R P R q (x ≫ φ) ht (c.trans b)
  have h' := congrArg (fun t : RigidifiedPair.Iso _ _ => t.iso ≪≫ e) h
  change (c.iso ≪≫ v ≪≫ e.symm) ≪≫ e = poincareKernelFrame A A P R P R q (x ≫ φ) ht at h'
  rw [CategoryTheory.Iso.trans_assoc, CategoryTheory.Iso.trans_assoc,
    CategoryTheory.Iso.symm_self_id, CategoryTheory.Iso.trans_refl] at h'
  exact h'.symm

set_option backward.isDefEq.respectTransparency false in
private theorem polarizedKernelRatioFrame_transition (hx : x ≫ (q).hom.hom = 1) :
    familyTransitionUnit q T (RigidifiedPair.map x B).bundle
      (polarizedKernelRatioFrame A P R L n x hx)
      (1 : T ⟶ A.X) x (𝟙 T) ((MonObj.one_comp (q).hom.hom).trans hx.symm) = 1 := by
  let V := (RigidifiedPair.map x B).bundle
  let v := polarizedKernelRatioFrame A P R L n x hx
  have hs : (lift ((1 : T ⟶ A.X) ≫ (q).hom.hom) (𝟙 T)).left = s := by
    rw [MonObj.one_comp, originSection_eq_unit_axis]
  have h₁ : (lift (1 : T ⟶ A.X) (𝟙 T)).left = s :=
    (originSection_eq_unit_axis A.X T).symm
  have h₂ := polarizedKernel_diagonal_mul A n x hx
  have h₀ := polarizedKernel_origin_mul A (T := T) n
  unfold familyTransitionUnit
  rw [TrivializedDescent.unit_congr p V v _ _ h₀ h₂ hs h₁ rfl]
  unfold TrivializedDescent.unit TrivializedDescent.transition
  rw [polarizedKernelRatioFrame_origin A P R L n x hx,
    polarizedKernelRatioFrame_diagonal A P R L n x hx, CategoryTheory.Iso.symm_self_id,
    TrivializedDescent.unitOfIso_refl]

variable [IsHProjective A.X.hom] [Smooth A.X.hom]

local notation "K" => Grp.X (MultiplicationKernel.kernelGroup A n)
local notation "i" => Mon.Hom.hom (InducedCategory.Hom.hom (Kernel.inclusion q))

set_option backward.isDefEq.respectTransparency false in
/-- The original polarization point on the actual multiplication kernel
lies in the kernel of the original dual pullback. -/
theorem polarizedKernel_comp_dualPullback :
    (i ≫ φ) ≫ picardIdentityComponentPullback P R P R (q).hom.hom = 1 := by
  let := picardCommGrpObj A.X.hom P R
  let D := picardIdentityComponent A.X.hom P R
  let : IsCommMonObj D := inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
  let f : A ⟶ Grp.mk D := lineBundleClassIdentityComponentGroupHom A.X P R (classOf A.X.left L)
  let t := MultiplicationKernel.map f n
  have ht : t.hom.hom ≫ (dualMultiplicationKernelInclusion A P R n).hom.hom = i ≫ φ :=
    congrArg (fun g : MultiplicationKernel.kernelGroup A n ⟶ Grp.mk D => g.hom.hom)
      (MultiplicationKernel.map_inclusion f n)
  rw [← ht, Category.assoc, dualMultiplicationKernelInclusion_comp_pullback A P R n,
    MonObj.comp_one]

set_option backward.isDefEq.respectTransparency false in
/-- The original kernel multiplier is one at the diagonal polarization
point on the native universal multiplication-kernel test. -/
theorem poincareKernelMultiplier_polarized_diagonal :
    Units.map (lift (𝟙 K) (𝟙 K)).left.appTop.hom.toMonoidHom
      (kernelMultiplier q (Kernel.marking q) K
        (poincarePullback A.X P R (i ≫ φ)).bundle
        (poincareKernelFrame A A P R P R q (i ≫ φ)
          (polarizedKernel_comp_dualPullback A P R L n))) = 1 := by
  let x : K ⟶ A.X := i
  let c := Kernel.marking q
  let Q := poincarePullback A.X P R (x ≫ φ)
  let b := poincareKernelFrame A A P R P R q (x ≫ φ)
    (polarizedKernel_comp_dualPullback A P R L n)
  have hx : x ≫ (q).hom.hom = 1 := Kernel.inclusion_comp_eq_one q
  let v := polarizedKernelRatioFrame A P R L n x hx
  let V := (RigidifiedPair.map x B).bundle
  let e := (poincarePullbackCompIso A.X P R x φ).iso
  have he := kernelMultiplier_eq_of_iso q c K Q.bundle b V e v
  change Units.map (lift (𝟙 K) (𝟙 K)).left.appTop.hom.toMonoidHom
    (kernelMultiplier q c K Q.bundle b) = 1
  rw [he]
  have h := familyTransitionUnit_kernel_translate q c K V v
    (1 : K ⟶ A.X) (𝟙 K) (𝟙 K)
  have hact : c.toTorsorAction.act (𝟙 K) (1 : K ⟶ A.X) = x := by
    change ((𝟙 K) ≫ x) * 1 = x
    rw [Category.id_comp, _root_.mul_one]
  refine h.symm.trans ?_
  unfold familyTransitionUnit
  exact (TrivializedDescent.unit_congr (familyMapOfHom (q).hom.hom K) V v
    _ _ _ _ rfl rfl (congrArg (fun t : K ⟶ A.X => (lift t (𝟙 K)).left) hact)).trans
    (polarizedKernelRatioFrame_transition A P R L n x hx)

end Polarized

end AlgebraicGeometry.Scheme.RelativePicard
