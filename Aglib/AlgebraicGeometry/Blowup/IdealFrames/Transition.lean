/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.IdealFrames

/-!
# Original blowup frame equations under further pullback

Actual native chart frames carry their original forward scalar equation.
The constructions below preserve this equation through affine pullback and
through displayed commuting chart squares. All frames and comparison maps
are constructed from the original supplier; a normal-frame family is not an input.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Hom Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Blowup.IdealFrames

/-- Pullback of a displayed unit frame through the actual unit comparison. -/
def pullbackFrame {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (e : SheafOfModules.unit Y.ringCatSheaf ≅ M) :
    SheafOfModules.unit X.ringCatSheaf ≅ (Scheme.Modules.pullback f).obj M :=
  (pullbackUnitIso f).symm ≪≫ (Scheme.Modules.pullback f).mapIso e

/-- Two successive pulls of an original frame retain the native composition comparison. -/
theorem pullbackFrame_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (e : SheafOfModules.unit Z.ringCatSheaf ≅ M) :
    pullbackFrame f (pullbackFrame g e) ≪≫ (pullbackComp f g).app M =
      pullbackFrame (f ≫ g) e := by
  apply Iso.ext
  simp only [pullbackFrame, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.map_comp, Iso.app_hom,
    Category.assoc]
  have hn := (pullbackComp f g).hom.naturality e.hom
  simp only [CategoryTheory.Functor.comp_map] at hn
  rw [hn]
  have hu : (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map (pullbackUnitIso g).inv ≫
      (pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf) =
      (pullbackUnitIso (f ≫ g)).inv := by
    apply (cancel_mono (pullbackUnitIso (f ≫ g)).hom).mp
    rw [Category.assoc, Category.assoc, pullbackUnitIso_comp,
      ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
    exact (pullbackUnitIso (f ≫ g)).inv_hom_id.symm
  rw [reassoc_of% hu]

/-- The actual composition comparisons obey the original three-arrow coherence equation. -/
theorem pullbackComp_assoc_hom {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app M) ≫
        (pullbackComp f (g ≫ h)).hom.app M ≫
        (pullbackCongr (Category.assoc f g h).symm).hom.app M =
      (pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
        (pullbackComp (f ≫ g) h).hom.app M := by
  have H := congrArg (fun η => η.app M) (pseudofunctor_associativity f g h)
  have ht : (pullbackComp f (g ≫ h)).inv.app M ≫
      (Scheme.Modules.pullback f).map ((pullbackComp g h).inv.app M) ≫
      (pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
      (pullbackComp (f ≫ g) h).hom.app M =
      (pullbackCongr (Category.assoc f g h).symm).hom.app M := by
    simpa only [NatTrans.comp_app, CategoryTheory.Functor.whiskerRight_app,
      CategoryTheory.Functor.whiskerLeft_app, CategoryTheory.Functor.associator_hom_app,
      Category.id_comp, pullbackCongr, eqToIso.hom] using H
  rw [← ht, Iso.hom_inv_id_app_assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- Transport a frame of the actual pullback along `j` to a further displayed factorization. -/
def frameAlong {X Y Z : Scheme.{u}} (f : X ⟶ Y) (j : Y ⟶ Z) (M : Z.Modules)
    (e : SheafOfModules.unit Y.ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M) :
    SheafOfModules.unit X.ringCatSheaf ≅ (Scheme.Modules.pullback (f ≫ j)).obj M :=
  pullbackFrame f e ≪≫ (pullbackComp f j).app M

/-- Normalized frame transport keeps the native three-arrow comparison. -/
theorem frameAlong_comp {W X Y Z : Scheme.{u}} (t : W ⟶ X) (f : X ⟶ Y) (j : Y ⟶ Z)
    (M : Z.Modules)
    (e : SheafOfModules.unit Y.ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M) :
    pullbackFrame t (frameAlong f j M e) ≪≫ (pullbackComp t (f ≫ j)).app M ≪≫
        (pullbackCongr (Category.assoc t f j).symm).app M =
      frameAlong (t ≫ f) j M e := by
  apply Iso.ext
  have he := congrArg Iso.hom (pullbackFrame_comp t f e)
  simp only [pullbackFrame, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.map_comp, Iso.app_hom,
    Category.assoc] at he
  simp only [frameAlong, pullbackFrame, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.map_comp, Iso.app_hom,
    Category.assoc]
  rw [pullbackComp_assoc_hom, reassoc_of% he]

/-- A frame followed by actual inverse component maps, in the same original module category. -/
def frameAfterMaps {C : Type*} [Category C] {U V W : C} (e : U ≅ V)
    (f : V ⟶ W) (g : W ⟶ V) (hfg : f ≫ g = 𝟙 V) (hgf : g ≫ f = 𝟙 W) : U ≅ W where
  hom := e.hom ≫ f
  inv := g ≫ e.inv
  hom_inv_id := by rw [Category.assoc, ← Category.assoc f, hfg, Category.id_comp, e.hom_inv_id]
  inv_hom_id := by rw [Category.assoc, Iso.inv_hom_id_assoc, hgf]

/-- The componentwise frame has exactly the original forward composite. -/
@[simp]
theorem frameAfterMaps_hom {C : Type*} [Category C] {U V W : C} (e : U ≅ V)
    (f : V ⟶ W) (g : W ⟶ V) (hfg : f ≫ g = 𝟙 V) (hgf : g ≫ f = 𝟙 W) :
    (frameAfterMaps e f g hfg hgf).hom = e.hom ≫ f := rfl

/-- The original scalar relation between two structure-module morphisms is preserved by
actual affine pullback and the native structure-module comparison. -/
theorem pullbackUnitHom_mul {S T : Type u} [CommRing S] [CommRing T]
    (φ : S →+* T) {M : (Spec (.of S)).Modules} (s : S)
    (e₀ e₁ : (show (Spec (.of S)).Modules from
      SheafOfModules.unit (Spec (.of S)).ringCatSheaf) ⟶ M)
    (he : e₁ = affineMultiplication S s ≫ e₀) :
    (pullbackUnitIso (Spec.map (CommRingCat.ofHom φ))).inv ≫
        (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).map e₁ =
      affineMultiplication T (φ s) ≫
        (pullbackUnitIso (Spec.map (CommRingCat.ofHom φ))).inv ≫
          (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).map e₀ := by
  rw [he, CategoryTheory.Functor.map_comp]
  have h :
      (pullbackUnitIso (Spec.map (CommRingCat.ofHom φ))).inv ≫
        (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).map
          (affineMultiplication S s) =
      affineMultiplication T (φ s) ≫
        (pullbackUnitIso (Spec.map (CommRingCat.ofHom φ))).inv := by
    apply (cancel_mono (pullbackUnitIso (Spec.map (CommRingCat.ofHom φ))).hom).mp
    rw [Category.assoc, affineMultiplication_pullback, Iso.inv_hom_id_assoc,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫
      (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).map e₀) h).trans
      (Category.assoc _ _ _))

/-- The forward pulled frame is the original unit comparison followed by the original
mapped arrow. -/
theorem pullbackFrame_hom {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (e : SheafOfModules.unit Y.ringCatSheaf ≅ M) :
    (pullbackFrame f e).hom =
      (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map e.hom := rfl

/-- A further frame factor preserves the actual forward pullback map. -/
theorem pullbackFrame_trans_hom {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : Y.Modules}
    (e : SheafOfModules.unit Y.ringCatSheaf ≅ M) (d : M ≅ N) :
    (pullbackFrame f (e ≪≫ d)).hom =
      (pullbackFrame f e).hom ≫ (Scheme.Modules.pullback f).map d.hom := by
  simp only [pullbackFrame, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.map_comp, Category.assoc]

/-- An original forward-frame factorization is preserved by native pullback. -/
theorem pullbackFrame_hom_factor {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : Y.Modules}
    (e : SheafOfModules.unit Y.ringCatSheaf ≅ M)
    (d : SheafOfModules.unit Y.ringCatSheaf ≅ N) (a : M ⟶ N)
    (h : d.hom = e.hom ≫ a) :
    (pullbackFrame f d).hom =
      (pullbackFrame f e).hom ≫ (Scheme.Modules.pullback f).map a := by
  simp only [pullbackFrame, Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom]
  rw [h, CategoryTheory.Functor.map_comp, Category.assoc]

/-- Postcomposing the base map of a frame retains the actual pullback associator. -/
theorem frameAlong_postcomp {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (j : X ⟶ Y) (k : Y ⟶ Z) (M : Z.Modules)
    (e : SheafOfModules.unit X.ringCatSheaf ≅
      (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback k).obj M)) :
    frameAlong f j ((Scheme.Modules.pullback k).obj M) e ≪≫
        (pullbackComp (f ≫ j) k).app M =
      frameAlong f (j ≫ k) M (e ≪≫ (pullbackComp j k).app M) ≪≫
        (pullbackCongr (Category.assoc f j k).symm).app M := by
  apply Iso.ext
  simp only [frameAlong, pullbackFrame, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.map_comp, Iso.app_hom,
    Category.assoc]
  rw [pullbackComp_assoc_hom]

/-- Equal original chart maps retain the actual equality comparison of pulled frames. -/
theorem frameAlong_congr_left {X Y Z : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (j : Y ⟶ Z) (M : Z.Modules)
    (e : SheafOfModules.unit Y.ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M) :
    frameAlong f j M e ≪≫ (pullbackCongr (congrArg (fun q => q ≫ j) h)).app M =
      frameAlong g j M e := by
  subst g
  apply Iso.ext
  simp [pullbackCongr]

/-- Reversing an actual morphism equality gives the inverse native pullback comparison. -/
theorem pullbackCongr_symm_app {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (M : Y.Modules) :
    ((pullbackCongr h).app M).symm = (pullbackCongr h.symm).app M := by
  subst g
  rfl

/-- The displayed equality on the original target map commutes with further frame pullback. -/
theorem frameAlong_congr_right {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    {j k : Y ⟶ Z} (h : j = k) (M : Z.Modules)
    (e : SheafOfModules.unit Y.ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M) :
    frameAlong f k M (e ≪≫ (pullbackCongr h).app M) =
      frameAlong f j M e ≪≫ (pullbackCongr (congrArg (fun q => f ≫ q) h)).app M := by
  subst k
  apply Iso.ext
  simp [frameAlong, pullbackFrame, pullbackCongr]

/-- A displayed square of the original chart maps preserves the original transported frame. -/
theorem frameAlong_square {W P O S X : Scheme.{u}}
    (p : W ⟶ P) (δ : P ⟶ S) (l : W ⟶ O) (r : O ⟶ S) (j : S ⟶ X)
    (h : p ≫ δ = l ≫ r) (M : X.Modules)
    (e : SheafOfModules.unit S.ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M) :
    frameAlong p (δ ≫ j) M (frameAlong δ j M e) ≪≫
        (pullbackCongr (Category.assoc p δ j).symm).app M ≪≫
        (pullbackCongr (congrArg (fun q => q ≫ j) h)).app M =
      frameAlong l (r ≫ j) M (frameAlong r j M e) ≪≫
        (pullbackCongr (Category.assoc l r j).symm).app M := by
  apply Iso.ext
  have h₀ := congrArg Iso.hom (frameAlong_comp p δ j M e)
  have h₁ := congrArg Iso.hom (frameAlong_comp l r j M e)
  have h₂ := congrArg Iso.hom (frameAlong_congr_left h j M e)
  simp only [frameAlong, Iso.trans_hom, Iso.app_hom, Category.assoc] at h₀ h₁ h₂ ⊢
  rw [reassoc_of% h₀, h₂, h₁]

/-- The total arrow equation is constructed from the two original displayed squares. -/
theorem frameSquareTotalEq {W P O S E X : Scheme.{u}}
    (p : W ⟶ P) (δ : P ⟶ S) (l : W ⟶ O) (r : O ⟶ S)
    (c : P ⟶ E) (i : E ⟶ X) (j : S ⟶ X)
    (hδ : p ≫ δ = l ≫ r) (hc : c ≫ i = δ ≫ j) :
    (p ≫ c) ≫ i = l ≫ (r ≫ j) := by
  rw [Category.assoc, hc, ← Category.assoc, hδ, Category.assoc]

/-- Actual conormal frame transport through the displayed original square is the
original pre-fibre ideal frame transported to that same source. -/
theorem frameAlong_ambient_square {W P O S E X : Scheme.{u}}
    (p : W ⟶ P) (δ : P ⟶ S) (l : W ⟶ O) (r : O ⟶ S)
    (c : P ⟶ E) (i : E ⟶ X) (j : S ⟶ X)
    (hδ : p ≫ δ = l ≫ r) (hc : c ≫ i = δ ≫ j) (M : X.Modules)
    (e : SheafOfModules.unit S.ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M)
    (d : SheafOfModules.unit P.ringCatSheaf ≅
      (Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback i).obj M))
    (hd : d ≪≫ (pullbackComp c i).app M =
      frameAlong δ j M e ≪≫ (pullbackCongr hc.symm).app M) :
    frameAlong p c ((Scheme.Modules.pullback i).obj M) d ≪≫
        (pullbackComp (p ≫ c) i).app M ≪≫
        (pullbackCongr (frameSquareTotalEq p δ l r c i j hδ hc)).app M ≪≫
        ((pullbackComp l (r ≫ j)).app M).symm =
      pullbackFrame l (frameAlong r j M e) := by
  have H := frameAlong_postcomp p c i M d
  rw [hd, frameAlong_congr_right] at H
  have Hhom := congrArg Iso.hom H
  simp only [Iso.trans_hom, Iso.app_hom, Category.assoc] at Hhom
  have hpath :
      (pullbackCongr (congrArg (fun q => p ≫ q) hc.symm)).hom.app M ≫
        (pullbackCongr (Category.assoc p c i).symm).hom.app M ≫
        (pullbackCongr (frameSquareTotalEq p δ l r c i j hδ hc)).hom.app M =
      (pullbackCongr (Category.assoc p δ j).symm).hom.app M ≫
        (pullbackCongr (congrArg (fun q => q ≫ j) hδ)).hom.app M ≫
        (pullbackCongr (Category.assoc l r j)).hom.app M := by
    simp only [pullbackCongr, eqToIso.hom, CategoryTheory.eqToHom_app, eqToHom_trans]
  have Hsquare := congrArg Iso.hom (frameAlong_square p δ l r j hδ M e)
  simp only [Iso.trans_hom, Iso.app_hom] at Hsquare
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  rw [reassoc_of% Hhom, reassoc_of% hpath, reassoc_of% Hsquare]
  simp only [pullbackCongr, eqToIso.hom, eqToHom_refl, NatTrans.id_app, Category.id_comp]
  simp only [frameAlong, Iso.trans_hom, Iso.app_hom, Category.assoc,
    Iso.hom_inv_id_app]
  exact Category.comp_id _

/-- Native comparison from centre pullback to pre-fibre pullback is compatible with the
original equality of the two centre maps and the original equality of the raw overlap maps. -/
theorem ambientComparison_congr {W E O X : Scheme.{u}}
    (l : W ⟶ O) (i : E ⟶ X) {q₀ q₁ : W ⟶ E} {r₀ r₁ : O ⟶ X}
    (hq : q₁ = q₀) (hr : r₁ = r₀)
    (h₀ : q₀ ≫ i = l ≫ r₀) (h₁ : q₁ ≫ i = l ≫ r₁) (M : X.Modules) :
    (pullbackCongr hq).app ((Scheme.Modules.pullback i).obj M) ≪≫
        (pullbackComp q₀ i).app M ≪≫ (pullbackCongr h₀).app M ≪≫
        ((pullbackComp l r₀).app M).symm =
      (pullbackComp q₁ i).app M ≪≫ (pullbackCongr h₁).app M ≪≫
        ((pullbackComp l r₁).app M).symm ≪≫
        (Scheme.Modules.pullback l).mapIso ((pullbackCongr hr).app M) := by
  subst q₁ r₁
  apply Iso.ext
  simp [pullbackCongr]

/-- Original forward frame equations transport through actual comparison isomorphisms. -/
theorem transportFrame_hom {C : Type*} [Category C] {U V₀ V₁ P₀ P₁ : C}
    (d₀ : U ≅ V₀) (d₁ : U ≅ V₁) (c : V₁ ≅ V₀)
    (C₀ : V₀ ≅ P₀) (C₁ : V₁ ≅ P₁) (R₀ : U ≅ P₀) (R₁ : U ≅ P₁)
    (r : P₁ ≅ P₀) (s : U ⟶ U)
    (h₀ : d₀ ≪≫ C₀ = R₀) (h₁ : d₁ ≪≫ C₁ = R₁)
    (hc : c ≪≫ C₀ = C₁ ≪≫ r)
    (hr : R₁.hom ≫ r.hom = s ≫ R₀.hom) :
    (d₁ ≪≫ c).hom = s ≫ d₀.hom := by
  apply (cancel_mono C₀.hom).mp
  have h₀' := congrArg Iso.hom h₀
  have h₁' := congrArg Iso.hom h₁
  have hc' := congrArg Iso.hom hc
  simp only [Iso.trans_hom] at h₀' h₁' hc' ⊢
  rw [Category.assoc, hc', ← Category.assoc, h₁', hr, ← h₀', Category.assoc]

end AlgebraicGeometry.Scheme.Blowup.IdealFrames
