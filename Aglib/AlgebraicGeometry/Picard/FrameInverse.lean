/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.IsomorphismSheaf.Inverse
public import Aglib.AlgebraicGeometry.Picard.FrameTensor
public import Aglib.AlgebraicGeometry.Picard.TrivializedPowerTorsor
public import Aglib.CategoryTheory.Sites.Torsor.CoefficientIso
public import Aglib.CategoryTheory.Sites.Torsor.InverseImage

/-! # Inverse frames on the original isomorphism sheaves

The coframe carrier is the actual sheaf `Isom(O,L)`, restricted and lifted in
exactly the same way as the native frame sheaf `Isom(L,O)`. Inversion is a
whole sheaf isomorphism. The existing coefficient and carrier transports
give its positive scalar torsor structure, whose literal action is proved
below. Its original augmentation Ext class is the negative native frame
class. The compatible-power comparison uses the original tensor powers and
unit normalization, for every natural level, including level one.

No comparison with a source Cech class, ordered cup, trace convention,
isogeny character, or Weil pairing is asserted here.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent
open AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor
open AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms
open AlgebraicGeometry.Scheme.EtaleCohomology
open GroupCohomology.Kummer.Coefficients

namespace CategoryTheory.Sheaf

universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The canonical coefficient inversion, in additive notation. -/
def coefficientNegIso (A : Sheaf J AddCommGrpCat.{w}) : A ≅ A where
  hom := -𝟙 A
  inv := -𝟙 A
  hom_inv_id := by simp
  inv_hom_id := by simp

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme.Modules.Invertible.FrameInverse

universe u

/-- The original opposite isomorphism sheaf, with the native restriction and lift. -/
def coframeSheaf (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u}) (L : LineBundle X) :
    SetSheaf X where
  obj := (Scheme.Etale.forget X).op ⋙
    (isoSheaf (ofLineBundle X (unitBundle X)) (ofLineBundle X L) h).obj ⋙
      uliftFunctor.{u + 1}
  property := by
    change Presheaf.IsSheaf (Scheme.smallEtaleTopology X)
      (((Scheme.Etale.forget X).op ⋙
        (isoSheaf (ofLineBundle X (unitBundle X)) (ofLineBundle X L) h).obj) ⋙
          uliftFunctor.{u + 1})
    apply Presheaf.isSheaf_comp_of_isSheaf _ _ uliftFunctor.{u + 1}
    apply (Scheme.Etale.forget X).op_comp_isSheaf_of_isSheaf
      (Scheme.smallEtaleTopology X) (Scheme.etaleTopology.over X)
    exact (isoSheaf (ofLineBundle X (unitBundle X)) (ofLineBundle X L) h).property

/-- The native whole inverse-Isom map, restricted to the small-etale site. -/
def frameInverseIso (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u}) (L : LineBundle X) :
    frameSheaf h X L ≅ coframeSheaf h X L where
  hom := ⟨{
    app U := TypeCat.ofHom fun s => ULift.up
      ((isoSheafInverse (ofLineBundle X L) (ofLineBundle X (unitBundle X)) h).hom.hom.app
        (op ((Scheme.Etale.forget X).obj U.unop)) s.down)
    naturality {_ _} _ := rfl }⟩
  inv := ⟨{
    app U := TypeCat.ofHom fun s => ULift.up
      ((isoSheafInverse (ofLineBundle X L) (ofLineBundle X (unitBundle X)) h).inv.hom.app
        (op ((Scheme.Etale.forget X).obj U.unop)) s.down)
    naturality {_ _} _ := rfl }⟩
  hom_inv_id := by ext U s; rfl
  inv_hom_id := by ext U s; rfl

/-- The native coframe sections are literal isomorphisms from O to the pulled bundle. -/
def coframeSectionsEquiv (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u}) (L : LineBundle X)
    (U : X.Etaleᵒᵖ) :
    (coframeSheaf h X L).obj.obj U ≃
      (SheafOfModules.unit U.unop.left.ringCatSheaf ≅
        (Scheme.Modules.pullback U.unop.hom).obj L.val) where
  toFun s := (frameSectionsEquiv h X L U ((frameInverseIso h X L).inv.hom.app U s)).symm
  invFun φ := (frameInverseIso h X L).hom.hom.app U
    ((frameSectionsEquiv h X L U).symm φ.symm)
  left_inv s := by
    change (frameInverseIso h X L).hom.hom.app U
      ((frameSectionsEquiv h X L U).symm
        (frameSectionsEquiv h X L U ((frameInverseIso h X L).inv.hom.app U s))) = s
    rw [Equiv.symm_apply_apply]
    rfl
  right_inv φ := by
    change (frameSectionsEquiv h X L U ((frameSectionsEquiv h X L U).symm φ.symm)).symm = φ
    rw [Equiv.apply_symm_apply]
    rfl

/-- The section comparison is exactly inversion of the native normalized frame. -/
@[simp] theorem coframeSectionsEquiv_inverse (h : EtaleLineBundleDescent.{u})
    (X : Scheme.{u}) (L : LineBundle X) (U : X.Etaleᵒᵖ)
    (s : (frameSheaf h X L).obj.obj U) :
    coframeSectionsEquiv h X L U ((frameInverseIso h X L).hom.hom.app U s) =
      (frameSectionsEquiv h X L U s).symm := rfl

/-- On the original raw coframe, normalization uses the inverse native unit pullback. -/
theorem coframeSectionsEquiv_hom (h : EtaleLineBundleDescent.{u})
    (X : Scheme.{u}) (L : LineBundle X) (U : X.Etaleᵒᵖ)
    (s : (coframeSheaf h X L).obj.obj U) :
    (coframeSectionsEquiv h X L U s).hom =
      (pullbackUnitIso U.unop.hom).inv ≫ s.down.val.1.hom := rfl

/-- Inversion is natural on the whole native small-etale carrier sheaves. -/
theorem frameInverse_naturality (h : EtaleLineBundleDescent.{u})
    (X : Scheme.{u}) (L : LineBundle X) {U V : X.Etaleᵒᵖ} (f : U ⟶ V) :
    (frameSheaf h X L).obj.map f ≫ (frameInverseIso h X L).hom.hom.app V =
      (frameInverseIso h X L).hom.hom.app U ≫ (coframeSheaf h X L).obj.map f :=
  (frameInverseIso h X L).hom.hom.naturality f

/-- Restriction is inverse native frame pullback, with all original unit comparisons. -/
theorem coframeSectionsEquiv_naturality (h : EtaleLineBundleDescent.{u})
    (X : Scheme.{u}) (L : LineBundle X) {U V : X.Etaleᵒᵖ} (f : U ⟶ V)
    (s : (coframeSheaf h X L).obj.obj U) :
    coframeSectionsEquiv h X L V ((coframeSheaf h X L).obj.map f s) =
      (TrivializedPowerTorsor.nativePullFrame L U.unop.hom V.unop.hom
        f.unop.left f.unop.w (coframeSectionsEquiv h X L U s).symm).symm := by
  apply congrArg Iso.symm
  apply Iso.ext
  exact TrivializedPowerTorsor.frameSections_restriction h X L f
    ((frameInverseIso h X L).inv.hom.app U s)

/-- The positive coframe torsor reuses the original torsor and canonical transports. -/
def coframeTorsor (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u}) (L : LineBundle X) :
    Torsor (gm X) :=
  ((frameTorsor h X L).ofCoefficientIso (Sheaf.coefficientNegIso (gm X))).transportCarrier
    (frameInverseIso h X L).symm

/-- The whole torsor comparison after canonical coefficient inversion. -/
def coframeCoefficientIso (h : EtaleLineBundleDescent.{u})
    (X : Scheme.{u}) (L : LineBundle X) :
    CategoryTheory.Sheaf.Torsor.Iso
      ((frameTorsor h X L).ofCoefficientIso (Sheaf.coefficientNegIso (gm X)))
      (coframeTorsor h X L) :=
  ((frameTorsor h X L).ofCoefficientIso (Sheaf.coefficientNegIso (gm X))).transportCarrierIso
    (frameInverseIso h X L).symm |>.symm

/-- The transported action is literal positive scalar postcomposition on coframes. -/
theorem coframeTorsor_action_sections (h : EtaleLineBundleDescent.{u})
    (X : Scheme.{u}) (L : LineBundle X) (U : X.Etaleᵒᵖ)
    (a : (gm X).obj.obj U) (s : (coframeSheaf h X L).obj.obj U) :
    coframeSectionsEquiv h X L U ((coframeTorsor h X L).action U a s) =
      coframeSectionsEquiv h X L U s ≪≫ scalarIso U.unop.left
        ((Scheme.Modules.pullback U.unop.hom).obj L.val) (unitsSections X U a).toMul := by
  change (frameSectionsEquiv h X L U
    (frameAction h X L U (-a) ((frameInverseIso h X L).inv.hom.app U s))).symm =
      (frameSectionsEquiv h X L U ((frameInverseIso h X L).inv.hom.app U s)).symm ≪≫
        scalarIso U.unop.left ((Scheme.Modules.pullback U.unop.hom).obj L.val)
          (unitsSections X U a).toMul
  rw [frameAction_sections]
  simpa only [map_neg, toMul_neg, inv_inv] using
    inverse_scalarIso U.unop.left
      (frameSectionsEquiv h X L U ((frameInverseIso h X L).inv.hom.app U s))
      (unitsSections X U (-a)).toMul

/-- Actual inverse frames are equivariant for the original coefficient inversion. -/
def frameInverseHom (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u}) (L : LineBundle X) :
    Torsor.Hom (-𝟙 (gm X)) (frameTorsor h X L) (coframeTorsor h X L) where
  map := (frameInverseIso h X L).hom
  equivariant U a s := by
    change (frameInverseIso h X L).hom.hom.app U (frameAction h X L U a s) =
      (frameInverseIso h X L).hom.hom.app U (frameAction h X L U (-(-a)) s)
    rw [neg_neg]

section ExtClass

universe w

/-- The original augmentation Ext class of positive coframes is the negative frame class. -/
theorem torsorExtClass_coframe (h : EtaleLineBundleDescent.{u})
    (X : Scheme.{u}) [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] (L : LineBundle X) :
    torsorExtClass (coframeTorsor h X L) = -torsorExtClass (frameTorsor h X L) := by
  have he := torsorExtClass_naturality (frameInverseHom h X L)
  change (torsorExtClass (frameTorsor h X L)).comp
    (Abelian.Ext.mk₀ (-𝟙 (gm X))) (add_zero 1) = _ at he
  rw [Abelian.Ext.mk₀_neg, Abelian.Ext.comp_neg, Abelian.Ext.comp_mk₀_id] at he
  exact he.symm

/-- This is the negative of the original native Picard class, using its existing frame bridge. -/
theorem torsorExtClass_coframe_picard (X : Scheme.{u})
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] (L : LineBundle X) :
    torsorExtClass (coframeTorsor etaleLineBundleDescent X L) =
      FrameTensor.picardH1Equiv.{u, w} X (-classOf X L) := by
  rw [map_neg, FrameTensor.picardH1Equiv_classOf]
  exact torsorExtClass_coframe etaleLineBundleDescent X L

end ExtClass

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower (Pair powerIso)
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower (unitLineBundle unitPowerIso)
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullback (pullbackPair)

/-- The actual normalized coframe power followed by the specified trivialization. -/
def coframePowerIso (X : Scheme.{u}) {n : ℕ} (P : Pair X n)
    (s : SheafOfModules.unit X.ringCatSheaf ≅ P.lineBundle.val) :
    SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.unit X.ringCatSheaf :=
  (unitPowerIso X n).symm ≪≫
    powerIso X (L := unitLineBundle X) (M := P.lineBundle) s n ≪≫ P.trivialization

/-- The normalized coframe power is the inverse of the original normalized frame power. -/
theorem coframePowerIso_inverse (X : Scheme.{u}) {n : ℕ} (P : Pair X n)
    (φ : P.lineBundle.val ≅ SheafOfModules.unit X.ringCatSheaf) :
    coframePowerIso X P φ.symm =
      (P.trivialization.symm ≪≫ powerIso X (M := unitLineBundle X) φ n ≪≫
        unitPowerIso X n).symm := by
  simp only [coframePowerIso, TrivializedPower.powerIso_symm, Iso.trans_symm, Iso.symm_symm_eq,
    Iso.trans_assoc]

/-- The actual inverse-frame power identity, with no positivity or invertibility premise. -/
theorem frame_power_iff_coframe_power (X : Scheme.{u}) {n : ℕ} (P : Pair X n)
    (φ : P.lineBundle.val ≅ SheafOfModules.unit X.ringCatSheaf) :
    (powerIso X (M := unitLineBundle X) φ n).hom ≫ (unitPowerIso X n).hom =
      P.trivialization.hom ↔ (coframePowerIso X P φ.symm).hom = 𝟙 _ := by
  unfold coframePowerIso
  rw [TrivializedPower.powerIso_symm]
  change (powerIso X (M := unitLineBundle X) φ n ≪≫ unitPowerIso X n).hom =
      P.trivialization.hom ↔
    (powerIso X (M := unitLineBundle X) φ n ≪≫ unitPowerIso X n).inv ≫
      P.trivialization.hom = 𝟙 _
  exact eq_comm.trans (Iso.inv_comp_eq_id _).symm

/-- The existing positive power value is one precisely when the inverse coframe is normalized. -/
theorem powerValue_eq_one_iff_inverse (X : Scheme.{u}) {n : ℕ} (P : Pair X n)
    (φ : P.lineBundle.val ≅ SheafOfModules.unit X.ringCatSheaf) :
    TrivializedPowerTorsor.powerValue X P φ = 1 ↔
      (coframePowerIso X P φ.symm).hom = 𝟙 _ :=
  (TrivializedPowerTorsor.powerValue_eq_one_iff X P φ).trans
    (frame_power_iff_coframe_power X P φ)

/-- Literal normalized coframes, on the same original power pair. -/
def CompatibleCoframe (X : Scheme.{u}) {n : ℕ} (P : Pair X n) :=
  {s : SheafOfModules.unit X.ringCatSheaf ≅ P.lineBundle.val //
    (coframePowerIso X P s).hom = 𝟙 _}

/-- Inversion identifies the original compatible frames with normalized coframes. -/
def compatibleInverseEquiv (X : Scheme.{u}) {n : ℕ} (P : Pair X n) :
    TrivializedPowerTorsor.CompatibleFrame X P ≃ CompatibleCoframe X P where
  toFun φ := ⟨φ.val.symm, (frame_power_iff_coframe_power X P φ.val).mp φ.property⟩
  invFun s := ⟨s.val.symm, (frame_power_iff_coframe_power X P s.val.symm).mpr s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Existing torsor sections are actual normalized coframes by inverse isomorphisms. -/
def inverseSectionsEquiv (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u})
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (P : Pair X n)
    (U : X.Etaleᵒᵖ) :
    (TrivializedPowerTorsor.torsor h X n hn hinv P).carrier.obj.obj U ≃
      CompatibleCoframe U.unop.left (pullbackPair U.unop.hom P) :=
  (TrivializedPowerTorsor.sectionsEquiv h X n hn hinv P U).trans
    (compatibleInverseEquiv U.unop.left (pullbackPair U.unop.hom P))

/-- Original root actions become inverse positive scalar actions on the actual coframes. -/
theorem inverseSectionsEquiv_action (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u})
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (P : Pair X n)
    (U : X.Etaleᵒᵖ) (ζ : (mu X n).obj.obj U)
    (s : (TrivializedPowerTorsor.torsor h X n hn hinv P).carrier.obj.obj U) :
    (inverseSectionsEquiv h X n hn hinv P U
      ((TrivializedPowerTorsor.torsor h X n hn hinv P).action U ζ s)).val =
      (inverseSectionsEquiv h X n hn hinv P U s).val ≪≫
        scalarIso U.unop.left ((Scheme.Modules.pullback U.unop.hom).obj P.lineBundle.val)
          ((rootsSections X n U (-ζ)).toMul : Γ(U.unop.left, ⊤)ˣ) := by
  change (TrivializedPowerTorsor.sectionsEquiv h X n hn hinv P U
    ((TrivializedPowerTorsor.torsor h X n hn hinv P).action U ζ s)).val.symm =
      (TrivializedPowerTorsor.sectionsEquiv h X n hn hinv P U s).val.symm ≪≫
        scalarIso U.unop.left (pullbackPair U.unop.hom P).lineBundle.val
          ((rootsSections X n U (-ζ)).toMul : Γ(U.unop.left, ⊤)ˣ)
  rw [TrivializedPowerTorsor.sectionsEquiv_action]
  simpa only [map_neg, toMul_neg, Subgroup.coe_inv] using
    inverse_scalarIso U.unop.left
      (TrivializedPowerTorsor.sectionsEquiv h X n hn hinv P U s).val
      ((rootsSections X n U ζ).toMul : Γ(U.unop.left, ⊤)ˣ)

/-- Inverse compatible sections restrict by the original native frame pullback. -/
theorem inverseSectionsEquiv_naturality (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u})
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (P : Pair X n)
    {U V : X.Etaleᵒᵖ} (f : U ⟶ V)
    (s : (TrivializedPowerTorsor.torsor h X n hn hinv P).carrier.obj.obj U) :
    (inverseSectionsEquiv h X n hn hinv P V
      ((TrivializedPowerTorsor.torsor h X n hn hinv P).carrier.obj.map f s)).val =
      (TrivializedPowerTorsor.nativePullFrame P.lineBundle U.unop.hom V.unop.hom
        f.unop.left f.unop.w (inverseSectionsEquiv h X n hn hinv P U s).val.symm).symm := by
  change (TrivializedPowerTorsor.sectionsEquiv h X n hn hinv P V
    ((TrivializedPowerTorsor.torsor h X n hn hinv P).carrier.obj.map f s)).val.symm =
      (TrivializedPowerTorsor.nativePullFrame P.lineBundle U.unop.hom V.unop.hom
        f.unop.left f.unop.w
        (TrivializedPowerTorsor.sectionsEquiv h X n hn hinv P U s).val).symm
  rw [TrivializedPowerTorsor.sectionsEquiv_naturality]

end AlgebraicGeometry.Scheme.Modules.Invertible.FrameInverse
