/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.OpenImmersion
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Square

/-!
# Canonical maps of actual conormal modules

The pullback of the actual kernel ideal along the original morphism is
functorial in commutative squares. Its canonical comparison respects pasting,
and an open ambient neighbourhood of the same source induces an isomorphism.
No closed-immersion, flatness, affineness or quasicoherence condition is needed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The canonical map between actual pulled-back kernel ideals for `i = i' ≫ b`,
using the identity on their common source. -/
def conormalMap {D X Y : Scheme.{u}}
    (i : D ⟶ X) (i' : D ⟶ Y) (b : Y ⟶ X) (h : i = i' ≫ b) :
    (Modules.pullback i).obj (idealModule i) ⟶
      (Modules.pullback i').obj (idealModule i') :=
  (pullbackCongr h).hom.app (idealModule i) ≫
    (pullbackComp i' b).inv.app (idealModule i) ≫
    (Modules.pullback i').map (idealPullbackMap i i' b (𝟙 D)
      (by simpa only [Category.id_comp] using h))

/-- The canonical map from the pulled-back original conormal along an actual square. -/
def conormalSquareMap {D D' X Y : Scheme.{u}}
    (i : D ⟶ X) (i' : D' ⟶ Y) (b : Y ⟶ X) (a : D' ⟶ D)
    (h : a ≫ i = i' ≫ b) :
    (Modules.pullback a).obj ((Modules.pullback i).obj (idealModule i)) ⟶
      (Modules.pullback i').obj (idealModule i') :=
  (pullbackComp a i).hom.app (idealModule i) ≫
    (pullbackCongr h).hom.app (idealModule i) ≫
      (pullbackComp i' b).inv.app (idealModule i) ≫
        (Modules.pullback i').map (idealPullbackMap i i' b a h)

private theorem pullbackComp_assoc_inv {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (M : D.Modules) :
    (pullbackComp (f ≫ g) h).inv.app M ≫
        (pullbackComp f g).inv.app ((Modules.pullback h).obj M) =
      (pullbackCongr (Category.assoc f g h)).hom.app M ≫
        (pullbackComp f (g ≫ h)).inv.app M ≫
          (Modules.pullback f).map ((pullbackComp g h).inv.app M) := by
  apply (cancel_mono ((pullbackComp f g).hom.app ((Modules.pullback h).obj M))).1
  apply (cancel_mono ((pullbackComp (f ≫ g) h).hom.app M)).1
  have hh := congrArg (fun q => (pullbackCongr (Category.assoc f g h)).hom.app M ≫ q.app M)
    (Scheme.Modules.pseudofunctor_associativity f g h)
  simpa [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc, pullbackCongr] using hh.symm

/-- Composition of actual ambient factorizations gives the same canonical conormal map. -/
theorem conormalMap_comp {D X Y Z : Scheme.{u}}
    (i₀ : D ⟶ X) (i₁ : D ⟶ Y) (i₂ : D ⟶ Z)
    (b₁ : Y ⟶ X) (b₂ : Z ⟶ Y) (h₁ : i₀ = i₁ ≫ b₁) (h₂ : i₁ = i₂ ≫ b₂) :
    conormalMap i₀ i₁ b₁ h₁ ≫ conormalMap i₁ i₂ b₂ h₂ =
      conormalMap i₀ i₂ (b₂ ≫ b₁) (by rw [h₁, h₂, Category.assoc]) := by
  subst i₀
  subst i₁
  let k₁ := idealPullbackMap ((i₂ ≫ b₂) ≫ b₁) (i₂ ≫ b₂) b₁ (𝟙 D) (by simp)
  let k₂ := idealPullbackMap (i₂ ≫ b₂) i₂ b₂ (𝟙 D) (by simp)
  let k₃ := idealPullbackMap ((i₂ ≫ b₂) ≫ b₁) i₂ (b₂ ≫ b₁) (𝟙 D)
    (by simp only [Category.id_comp, Category.assoc])
  have hk : (pullbackComp b₂ b₁).inv.app (idealModule ((i₂ ≫ b₂) ≫ b₁)) ≫
      (Modules.pullback b₂).map k₁ ≫ k₂ = k₃ := by
    simpa only [Category.id_comp] using
      idealPullbackMap_comp ((i₂ ≫ b₂) ≫ b₁) (i₂ ≫ b₂) i₂ b₁ b₂
        (𝟙 D) (𝟙 D) (by simp) (by simp)
  change ((pullbackComp (i₂ ≫ b₂) b₁).inv.app _ ≫
      (Modules.pullback (i₂ ≫ b₂)).map k₁) ≫
        ((pullbackComp i₂ b₂).inv.app _ ≫ (Modules.pullback i₂).map k₂) =
    (pullbackCongr (Category.assoc i₂ b₂ b₁)).hom.app _ ≫
      (pullbackComp i₂ (b₂ ≫ b₁)).inv.app _ ≫ (Modules.pullback i₂).map k₃
  simp only [Category.assoc]
  rw [(pullbackComp i₂ b₂).inv.naturality_assoc k₁]
  simp only [Functor.comp_map]
  rw [← Category.assoc, pullbackComp_assoc_inv]
  rw [← hk]
  simp only [Functor.map_comp, Category.assoc]

/-- An open ambient neighbourhood containing the same original section has the same conormal. -/
theorem conormalMap_isIso_of_isOpenImmersion {D X Y : Scheme.{u}}
    (i : D ⟶ X) (i' : D ⟶ Y) (b : Y ⟶ X) (h : i = i' ≫ b) [IsOpenImmersion b] :
    IsIso (conormalMap i i' b h) := by
  have hs : (𝟙 D) ≫ i = i' ≫ b := by simpa only [Category.id_comp] using h
  let : IsIso (idealPullbackMap i i' b (𝟙 D) hs) :=
    idealPullbackMap_isIso_of_isOpenImmersion i i' b (𝟙 D) hs
      (IsPullback.of_horiz_isIso_mono ⟨hs⟩)
  dsimp only [conormalMap]
  infer_instance

open Scheme.Modules.BaseChange.Affine.Square

private theorem pullbackSquare_comp
    {D₀ D₁ D₂ X₀ X₁ X₂ : Scheme.{u}}
    (s₀ : D₀ ⟶ X₀) (s₁ : D₁ ⟶ X₁) (s₂ : D₂ ⟶ X₂)
    (a₁ : D₁ ⟶ D₀) (a₂ : D₂ ⟶ D₁) (b₁ : X₁ ⟶ X₀) (b₂ : X₂ ⟶ X₁)
    (h₁ : a₁ ≫ s₀ = s₁ ≫ b₁) (h₂ : a₂ ≫ s₁ = s₂ ≫ b₂) :
    Functor.whiskerLeft (Modules.pullback s₀) (pullbackComp a₂ a₁).inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (pullbackSquareIso s₁ a₁ b₁ s₀ h₁.symm).hom
        (Modules.pullback a₂) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (Modules.pullback b₁)
        (pullbackSquareIso s₂ a₂ b₂ s₁ h₂.symm).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (pullbackComp b₂ b₁).hom (Modules.pullback s₂) =
    (pullbackSquareIso s₂ (a₂ ≫ a₁) (b₂ ≫ b₁) s₀
      (by symm; rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc])).hom := by
  apply (conjugateEquiv
    ((pullbackPushforwardAdjunction (b₂ ≫ b₁)).comp (pullbackPushforwardAdjunction s₂))
    ((pullbackPushforwardAdjunction s₀).comp
      (pullbackPushforwardAdjunction (a₂ ≫ a₁)))).injective
  rw [conjugateEquiv_pullbackSquareIso]
  simp only [← Category.assoc]
  rw [← conjugateEquiv_comp _
    (((pullbackPushforwardAdjunction b₁).comp
      (pullbackPushforwardAdjunction b₂)).comp (pullbackPushforwardAdjunction s₂)) _]
  rw [← conjugateEquiv_comp _
    ((pullbackPushforwardAdjunction b₁).comp
      ((pullbackPushforwardAdjunction b₂).comp (pullbackPushforwardAdjunction s₂))) _]
  rw [← conjugateEquiv_comp _
    ((pullbackPushforwardAdjunction b₁).comp
      ((pullbackPushforwardAdjunction s₁).comp (pullbackPushforwardAdjunction a₂))) _]
  rw [← conjugateEquiv_comp _
    (((pullbackPushforwardAdjunction b₁).comp
      (pullbackPushforwardAdjunction s₁)).comp (pullbackPushforwardAdjunction a₂)) _]
  rw [← conjugateEquiv_comp _
    (((pullbackPushforwardAdjunction s₀).comp
      (pullbackPushforwardAdjunction a₁)).comp (pullbackPushforwardAdjunction a₂)) _]
  rw [← conjugateEquiv_comp _
    ((pullbackPushforwardAdjunction s₀).comp
      ((pullbackPushforwardAdjunction a₁).comp (pullbackPushforwardAdjunction a₂))) _]
  rw [conjugateEquiv_whiskerRight,
    Scheme.Modules.BaseChange.Affine.Square.conjugateEquiv_pullbackComp_hom,
    conjugateEquiv_associator_inv, conjugateEquiv_whiskerLeft,
    conjugateEquiv_pullbackSquareIso, conjugateEquiv_associator_hom,
    conjugateEquiv_whiskerRight, conjugateEquiv_pullbackSquareIso,
    conjugateEquiv_associator_inv, conjugateEquiv_whiskerLeft,
    Scheme.Modules.conjugateEquiv_pullbackComp_inv]
  ext M U
  simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app, Category.id_comp]
  unfold pushforwardSquareIso
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app, Category.id_comp, Category.comp_id,
    Scheme.Modules.pushforward_obj_presheaf_map]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]
  rw [← Functor.map_comp]
  congr 1

private theorem pullbackSquare_comp_app
    {D₀ D₁ D₂ X₀ X₁ X₂ : Scheme.{u}}
    (s₀ : D₀ ⟶ X₀) (s₁ : D₁ ⟶ X₁) (s₂ : D₂ ⟶ X₂)
    (a₁ : D₁ ⟶ D₀) (a₂ : D₂ ⟶ D₁) (b₁ : X₁ ⟶ X₀) (b₂ : X₂ ⟶ X₁)
    (h₁ : a₁ ≫ s₀ = s₁ ≫ b₁) (h₂ : a₂ ≫ s₁ = s₂ ≫ b₂) (M : X₀.Modules) :
    (Modules.pullback a₂).map ((pullbackSquareIso s₁ a₁ b₁ s₀ h₁.symm).hom.app M) ≫
      (pullbackSquareIso s₂ a₂ b₂ s₁ h₂.symm).hom.app ((Modules.pullback b₁).obj M) =
    (pullbackComp a₂ a₁).hom.app ((Modules.pullback s₀).obj M) ≫
      (pullbackSquareIso s₂ (a₂ ≫ a₁) (b₂ ≫ b₁) s₀
        (by symm; rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc])).hom.app M ≫
          (Modules.pullback s₂).map ((pullbackComp b₂ b₁).inv.app M) := by
  apply (cancel_epi ((pullbackComp a₂ a₁).inv.app ((Modules.pullback s₀).obj M))).1
  apply (cancel_mono ((Modules.pullback s₂).map ((pullbackComp b₂ b₁).hom.app M))).1
  have h := congrArg (fun q => q.app M) (pullbackSquare_comp s₀ s₁ s₂ a₁ a₂ b₁ b₂ h₁ h₂)
  have hmap := ((Modules.pullback s₂).mapIso ((pullbackComp b₂ b₁).app M)).inv_hom_id
  change (Modules.pullback s₂).map ((pullbackComp b₂ b₁).inv.app M) ≫
    (Modules.pullback s₂).map ((pullbackComp b₂ b₁).hom.app M) = 𝟙 _ at hmap
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at h
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [hmap, Category.comp_id]
  exact h

/-- Canonical maps on actual pulled-back ideals respect pasting of the original squares. -/
theorem conormalSquareMap_comp
    {D₀ D₁ D₂ X₀ X₁ X₂ : Scheme.{u}}
    (s₀ : D₀ ⟶ X₀) (s₁ : D₁ ⟶ X₁) (s₂ : D₂ ⟶ X₂)
    (a₁ : D₁ ⟶ D₀) (a₂ : D₂ ⟶ D₁) (b₁ : X₁ ⟶ X₀) (b₂ : X₂ ⟶ X₁)
    (h₁ : a₁ ≫ s₀ = s₁ ≫ b₁) (h₂ : a₂ ≫ s₁ = s₂ ≫ b₂) :
    (Modules.pullback a₂).map (conormalSquareMap s₀ s₁ b₁ a₁ h₁) ≫
      conormalSquareMap s₁ s₂ b₂ a₂ h₂ =
    (pullbackComp a₂ a₁).hom.app ((Modules.pullback s₀).obj (idealModule s₀)) ≫
      conormalSquareMap s₀ s₂ (b₂ ≫ b₁) (a₂ ≫ a₁)
        (by rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc]) := by
  let q₁ := pullbackSquareIso s₁ a₁ b₁ s₀ h₁.symm
  let q₂ := pullbackSquareIso s₂ a₂ b₂ s₁ h₂.symm
  let q₃ := pullbackSquareIso s₂ (a₂ ≫ a₁) (b₂ ≫ b₁) s₀
    (by symm; rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc])
  let k₁ := idealPullbackMap s₀ s₁ b₁ a₁ h₁
  let k₂ := idealPullbackMap s₁ s₂ b₂ a₂ h₂
  let k₃ := idealPullbackMap s₀ s₂ (b₂ ≫ b₁) (a₂ ≫ a₁)
    (by rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc])
  change (Modules.pullback a₂).map
      (q₁.hom.app (idealModule s₀) ≫ (Modules.pullback s₁).map k₁) ≫
      (q₂.hom.app (idealModule s₁) ≫ (Modules.pullback s₂).map k₂) =
    (pullbackComp a₂ a₁).hom.app _ ≫
      q₃.hom.app (idealModule s₀) ≫ (Modules.pullback s₂).map k₃
  simp only [Functor.map_comp, Category.assoc]
  have hn := q₂.hom.naturality k₁
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [← Category.assoc, pullbackSquare_comp_app s₀ s₁ s₂ a₁ a₂ b₁ b₂ h₁ h₂]
  have hk := idealPullbackMap_comp s₀ s₁ s₂ b₁ b₂ a₁ a₂ h₁ h₂
  change (pullbackComp b₂ b₁).inv.app (idealModule s₀) ≫
    (Modules.pullback b₂).map k₁ ≫ k₂ = k₃ at hk
  rw [← hk]
  simp only [q₃, Functor.map_comp, Category.assoc]


private theorem pullbackComp_id_source_hom {D X : Scheme.{u}}
    (i : D ⟶ X) (M : X.Modules) :
    (pullbackComp (𝟙 D) i).hom.app M ≫
      (pullbackCongr (Category.id_comp i)).hom.app M =
    (pullbackId D).hom.app ((Modules.pullback i).obj M) := by
  apply (cancel_epi ((pullbackComp (𝟙 D) i).inv.app M)).1
  have h := congrArg (fun q => q.app M) (Scheme.Modules.pseudofunctor_right_unitality i)
  simpa [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Category.assoc, pullbackCongr] using h.symm

private theorem pullbackComp_id_ambient_hom {D X : Scheme.{u}}
    (i : D ⟶ X) (M : X.Modules) :
    (pullbackComp i (𝟙 X)).hom.app M ≫
      (pullbackCongr (Category.comp_id i)).hom.app M =
    (Modules.pullback i).map ((pullbackId X).hom.app M) := by
  apply (cancel_epi ((pullbackComp i (𝟙 X)).inv.app M)).1
  have h := congrArg (fun q => q.app M) (Scheme.Modules.pseudofunctor_left_unitality i)
  simpa [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Category.assoc, pullbackCongr] using h.symm

/-- Equality of the original source maps retains the canonical square map. -/
theorem conormalSquareMap_source_congr {D D' X Y : Scheme.{u}}
    (i : D ⟶ X) (i' : D' ⟶ Y) (b : Y ⟶ X) {a a' : D' ⟶ D}
    (h : a = a') (hs : a ≫ i = i' ≫ b) (hs' : a' ≫ i = i' ≫ b) :
    (pullbackCongr h).hom.app ((Modules.pullback i).obj (idealModule i)) ≫
      conormalSquareMap i i' b a' hs' = conormalSquareMap i i' b a hs := by
  cases h
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]

/-- The square map with identity source map is the original same-source comparison. -/
theorem conormalSquareMap_id_source {D X Y : Scheme.{u}}
    (i : D ⟶ X) (i' : D ⟶ Y) (b : Y ⟶ X) (h : i = i' ≫ b) :
    conormalSquareMap i i' b (𝟙 D) (by simpa only [Category.id_comp] using h) =
      (pullbackId D).hom.app ((Modules.pullback i).obj (idealModule i)) ≫
        conormalMap i i' b h := by
  have hc : (pullbackCongr (show (𝟙 D) ≫ i = i' ≫ b from
      (Category.id_comp i).trans h)).hom.app (idealModule i) =
      (pullbackCongr (Category.id_comp i)).hom.app (idealModule i) ≫
        (pullbackCongr h).hom.app (idealModule i) := by
    simp [pullbackCongr]
  dsimp only [conormalSquareMap, conormalMap]
  conv_lhs => rw [hc]
  simp only [← Category.assoc]
  rw [pullbackComp_id_source_hom]

/-- An ambient factorization can be pasted after the original general square map. -/
theorem conormalSquareMap_comp_ambient {D₀ D X₀ X₁ X₂ : Scheme.{u}}
    (s₀ : D₀ ⟶ X₀) (s₁ : D ⟶ X₁) (s₂ : D ⟶ X₂)
    (a : D ⟶ D₀) (b₁ : X₁ ⟶ X₀) (b₂ : X₂ ⟶ X₁)
    (h₁ : a ≫ s₀ = s₁ ≫ b₁) (h₂ : s₁ = s₂ ≫ b₂) :
    conormalSquareMap s₀ s₁ b₁ a h₁ ≫ conormalMap s₁ s₂ b₂ h₂ =
      conormalSquareMap s₀ s₂ (b₂ ≫ b₁) a
        (by rw [h₁, h₂, Category.assoc]) := by
  let hs₂ : (𝟙 D) ≫ s₁ = s₂ ≫ b₂ := by simpa only [Category.id_comp] using h₂
  have H := conormalSquareMap_comp s₀ s₁ s₂ a (𝟙 D) b₁ b₂ h₁ hs₂
  rw [conormalSquareMap_id_source s₁ s₂ b₂ h₂] at H
  have hn := (pullbackId D).hom.naturality (conormalSquareMap s₀ s₁ b₁ a h₁)
  dsimp only [Functor.id_map] at hn
  rw [reassoc_of% hn] at H
  rw [← conormalSquareMap_source_congr s₀ s₂ (b₂ ≫ b₁) (Category.id_comp a)
    (by rw [Category.assoc, h₁, ← Category.assoc, hs₂, Category.assoc])
    (by rw [h₁, h₂, Category.assoc])] at H
  rw [reassoc_of% (pullbackComp_id_source_hom a
    ((Modules.pullback s₀).obj (idealModule s₀)))] at H
  exact (cancel_epi ((pullbackId D).hom.app
    ((Modules.pullback a).obj ((Modules.pullback s₀).obj (idealModule s₀))))).1 H

/-- Pulling back an ambient factorization and pasting the original square gives its composite. -/
theorem conormalMap_comp_square {D D' X₀ X₁ X₂ : Scheme.{u}}
    (s₀ : D ⟶ X₀) (s₁ : D ⟶ X₁) (s₂ : D' ⟶ X₂)
    (a : D' ⟶ D) (b₁ : X₁ ⟶ X₀) (b₂ : X₂ ⟶ X₁)
    (h₁ : s₀ = s₁ ≫ b₁) (h₂ : a ≫ s₁ = s₂ ≫ b₂) :
    (Modules.pullback a).map (conormalMap s₀ s₁ b₁ h₁) ≫
      conormalSquareMap s₁ s₂ b₂ a h₂ =
    conormalSquareMap s₀ s₂ (b₂ ≫ b₁) a
      (by rw [h₁, ← Category.assoc, h₂, Category.assoc]) := by
  let hs₁ : (𝟙 D) ≫ s₀ = s₁ ≫ b₁ := by simpa only [Category.id_comp] using h₁
  have H := conormalSquareMap_comp s₀ s₁ s₂ (𝟙 D) a b₁ b₂ hs₁ h₂
  rw [conormalSquareMap_id_source s₀ s₁ b₁ h₁] at H
  simp only [Functor.map_comp, Category.assoc] at H
  rw [← conormalSquareMap_source_congr s₀ s₂ (b₂ ≫ b₁) (Category.comp_id a)
    (by rw [Category.assoc, hs₁, ← Category.assoc, h₂, Category.assoc])
    (by rw [h₁, ← Category.assoc, h₂, Category.assoc])] at H
  rw [reassoc_of% (pullbackComp_id_ambient_hom a
    ((Modules.pullback s₀).obj (idealModule s₀)))] at H
  exact (cancel_epi ((Modules.pullback a).map ((pullbackId D).hom.app
    ((Modules.pullback s₀).obj (idealModule s₀))))).1 H

end AlgebraicGeometry.Scheme.Hom
