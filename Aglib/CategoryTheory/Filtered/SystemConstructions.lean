/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.SectionArrows
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.ConeExtension

/-! # Actual restrictions and pullbacks of coefficient systems

Every system is constructed from the one original coherent adjunction data.
Restriction is flattened along the actual composite indexing functor. Square
pullback and fixed-source transitions retain their original whole comparisons;
identity, composition and left-map values are proved, not input system laws.
No abelian, injective, exactness or colimit capability is needed.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.InjectiveSystem

universe uJ vJ uA vA uI vI uK vK

variable {J : Type uJ} [Category.{vJ} J]
  {A : J → Type uA} [∀ j, Category.{vA} (A j)]
  (D : AdjunctionData A)
  {I : Type uI} [Category.{vI} I] (X : I ⥤ J)

private theorem restricted_map_id (F : System (D.reindex X)) {i : I}
    (a : i ⟶ i) (ha : a = 𝟙 i) (he : X.map a = 𝟙 (X.obj i)) :
    F.map a ≫ eqToHom (congrArg (fun f => (D.right f).obj (F.obj i)) he) ≫
      (D.idIso (X.obj i)).hom.app (F.obj i) = 𝟙 (F.obj i) := by
  cases ha
  simpa only [AdjunctionData.reindex, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app, Category.assoc] using F.map_id i

private theorem restricted_map_comp (F : System (D.reindex X)) {i j k : I}
    (a : i ⟶ j) (b : j ⟶ k) (t : i ⟶ k) (ht : t = a ≫ b)
    (he : X.map t = X.map a ≫ X.map b) :
    F.map t ≫ eqToHom (congrArg (fun f => (D.right f).obj (F.obj k)) he) ≫
      (D.compIso (X.map a) (X.map b)).hom.app (F.obj k) =
        F.map a ≫ (D.right (X.map a)).map (F.map b) := by
  cases ht
  simpa only [AdjunctionData.reindex, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app, Category.assoc] using F.map_comp a b

/-- Restrict actual transitions directly to the flattened original indexing composite. -/
def System.restrictAlong {K : Type uK} [Category.{vK} K]
    (F : System (D.reindex X)) (s : K ⥤ I) : System (D.reindex (s ⋙ X)) where
  obj k := F.obj (s.obj k)
  map a := F.map (s.map a)
  map_id k := by
    simpa only [AdjunctionData.reindex, Functor.comp_obj, Functor.comp_map,
      Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app, Category.assoc] using
      restricted_map_id D X F (s.map (𝟙 k)) (s.map_id k) ((s ⋙ X).map_id k)
  map_comp a b := by
    simpa only [AdjunctionData.reindex, Functor.comp_obj, Functor.comp_map,
      Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app, Category.assoc] using
      restricted_map_comp D X F (s.map a) (s.map b) (s.map (a ≫ b))
        (s.map_comp a b) ((s ⋙ X).map_comp a b)

/-- The flattened restriction keeps the literal original left transition. -/
@[simp]
theorem System.restrictAlong_leftMap {K : Type uK} [Category.{vK} K]
    (F : System (D.reindex X)) (s : K ⥤ I) {i j : K} (a : i ⟶ j) :
    (F.restrictAlong D X s).leftMap (D.reindex (s ⋙ X)) a =
      F.leftMap (D.reindex X) (s.map a) := rfl

section Pullback

variable (Y : I ⥤ J) (τ : X ⟶ Y) (F : System (D.reindex X))

/-- Pull the original transition across the actual naturality square. -/
def System.pullbackTransition {i j : I} (a : i ⟶ j) :
    (D.left (Y.map a)).obj ((D.left (τ.app i)).obj (F.obj i)) ⟶
      (D.left (τ.app j)).obj (F.obj j) :=
  D.squareCoefficientMap (τ.app i) (τ.app j) (X.map a) (Y.map a)
    (τ.naturality a) (F.leftMap (D.reindex X) a)

variable (hD : D.Coherent)

include hD in
/-- Original square units imply the actual pulled-system identity law. -/
theorem System.pullbackTransition_id (i : I) :
    pullbackTransition D X Y τ F (𝟙 i) =
      ((D.reindex Y).leftIdIso i).hom.app ((D.left (τ.app i)).obj (F.obj i)) := by
  have ht := D.squareCoefficientMap_transport (τ.app i) (τ.app i)
    (𝟙 (X.obj i)) (X.map (𝟙 i)) (𝟙 (Y.obj i)) (Y.map (𝟙 i))
    (X.map_id i) (Y.map_id i)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    (τ.naturality (𝟙 i)) ((D.leftIdIso (X.obj i)).hom.app (F.obj i))
  rw [D.squareCoefficientMap_id hD] at ht
  dsimp only [pullbackTransition]
  rw [AdjunctionData.Sections.systemTransition_id]
  rw [D.leftIdIso_reindex Y i]
  simpa only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app] using ht

include hD in
/-- Actual horizontal square pasting implies the pulled-system composition law. -/
theorem System.pullbackTransition_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    pullbackTransition D X Y τ F (a ≫ b) =
      ((D.reindex Y).leftCompIso a b).hom.app ((D.left (τ.app i)).obj (F.obj i)) ≫
        (D.left (Y.map b)).map (pullbackTransition D X Y τ F a) ≫
          pullbackTransition D X Y τ F b := by
  let e : (X.map a ≫ X.map b) ≫ τ.app k = τ.app i ≫ (Y.map a ≫ Y.map b) := by
    rw [Category.assoc, τ.naturality b, ← Category.assoc, τ.naturality a, Category.assoc]
  let φ := (D.leftCompIso (X.map a) (X.map b)).hom.app (F.obj i) ≫
    (D.left (X.map b)).map (F.leftMap (D.reindex X) a) ≫ F.leftMap (D.reindex X) b
  let v := eqToHom (congrArg
    (fun h => (D.left h).obj ((D.left (τ.app i)).obj (F.obj i))) (Y.map_comp a b))
  have htransition : F.leftMap (D.reindex X) (a ≫ b) =
      eqToHom (congrArg (fun h => (D.left h).obj (F.obj i)) (X.map_comp a b)) ≫ φ := by
    simpa only [eqToIso.hom, eqToHom_app, φ] using
      AdjunctionData.Sections.systemTransition_comp X F a b
  have ht := D.squareCoefficientMap_transport (τ.app i) (τ.app k)
    (X.map a ≫ X.map b) (X.map (a ≫ b))
    (Y.map a ≫ Y.map b) (Y.map (a ≫ b))
    (X.map_comp a b) (Y.map_comp a b) e (τ.naturality (a ≫ b)) φ
  have hp : (D.leftCompIso (Y.map a) (Y.map b)).hom.app ((D.left (τ.app i)).obj (F.obj i)) ≫
        (D.left (Y.map b)).map (pullbackTransition D X Y τ F a) ≫
          pullbackTransition D X Y τ F b =
      D.squareCoefficientMap (τ.app i) (τ.app k) (X.map a ≫ X.map b)
        (Y.map a ≫ Y.map b) e φ :=
    D.squareCoefficientMap_hComp hD (τ.app i) (τ.app j) (τ.app k)
      (X.map a) (X.map b) (Y.map a) (Y.map b) (τ.naturality a) (τ.naturality b) e
      (F.leftMap (D.reindex X) a) (F.leftMap (D.reindex X) b)
  have hc : pullbackTransition D X Y τ F (a ≫ b) =
      v ≫ D.squareCoefficientMap (τ.app i) (τ.app k) (X.map a ≫ X.map b)
        (Y.map a ≫ Y.map b) e φ := by
    dsimp only [pullbackTransition]
    rw [htransition]
    exact ht
  have hy : ((D.reindex Y).leftCompIso a b).hom.app ((D.left (τ.app i)).obj (F.obj i)) =
      v ≫ (D.leftCompIso (Y.map a) (Y.map b)).hom.app ((D.left (τ.app i)).obj (F.obj i)) := by
    simpa only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app, v] using
      congrArg (fun t => t.hom.app ((D.left (τ.app i)).obj (F.obj i)))
        (D.leftCompIso_reindex Y a b)
  have hz := congrArg
    (fun z : (D.left (Y.map (a ≫ b))).obj ((D.left (τ.app i)).obj (F.obj i)) ⟶
      (D.left (Y.map b)).obj ((D.left (Y.map a)).obj ((D.left (τ.app i)).obj (F.obj i))) =>
        z ≫ (D.left (Y.map b)).map (pullbackTransition D X Y τ F a) ≫
          pullbackTransition D X Y τ F b) hy
  have hv := (Category.assoc v
    ((D.leftCompIso (Y.map a) (Y.map b)).hom.app ((D.left (τ.app i)).obj (F.obj i)))
    ((D.left (Y.map b)).map (pullbackTransition D X Y τ F a) ≫
      pullbackTransition D X Y τ F b)).symm.trans hz.symm
  exact hc.trans ((congrArg (fun z => v ≫ z) hp.symm).trans hv)

include hD in
/-- The actual objects and square transitions form a genuine compatible system. -/
def System.pullback : System (D.reindex Y) :=
  System.ofLeft (D.reindex Y)
    (fun i => (D.left (τ.app i)).obj (F.obj i))
    (System.pullbackTransition D X Y τ F)
    (System.pullbackTransition_id D X Y τ F hD)
    (fun a b => System.pullbackTransition_comp D X Y τ F hD a b)

/-- The constructor recovers the SAME original coefficient square, not a replacement map. -/
@[simp]
theorem System.pullback_leftMap {i j : I} (a : i ⟶ j) :
    (System.pullback D X Y τ F hD).leftMap (D.reindex Y) a =
      System.pullbackTransition D X Y τ F a :=
  System.ofLeft_leftMap (D.reindex Y)
    (fun i => (D.left (τ.app i)).obj (F.obj i))
    (System.pullbackTransition D X Y τ F)
    (System.pullbackTransition_id D X Y τ F hD)
    (fun a b => System.pullbackTransition_comp D X Y τ F hD a b) a

end Pullback

section FixedSource

variable (hD : D.Coherent)

include hD in
/-- Fixed-source inverse triangles retain identity-arrow equality transport. -/
theorem fixedSourceTriangle_id {x y : J} (p : x ⟶ y) (a : y ⟶ y)
    (ha : a = 𝟙 y) (h : p ≫ a = p) (F : A x) :
    (D.triangleIso p p a h).inv.app F =
      (eqToIso (congrArg D.left ha) ≪≫ D.leftIdIso y).hom.app ((D.left p).obj F) := by
  cases ha
  apply (cancel_epi ((D.triangleIso p p (𝟙 y) h).hom.app F)).mp
  have hu := congrArg (fun e => e.hom.app F) (D.leftCompIso_comp_id_whole hD p)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, eqToIso.hom,
    eqToHom_app] at hu
  let l := (D.leftCompIso p (𝟙 y)).hom.app F
  let m := (D.leftIdIso y).hom.app ((D.left p).obj F)
  change l ≫ m ≫ 𝟙 _ =
    eqToHom (congrArg (fun f => (D.left f).obj F) (Category.comp_id p)) at hu
  have hu' := (congrArg (fun z => l ≫ z) (Category.comp_id m)).symm.trans hu
  let e := eqToHom (congrArg (fun f => (D.left f).obj F) (Category.comp_id p).symm)
  have ht := congrArg (fun z => e ≫ z) hu'
  have hT : (D.triangleIso p p (𝟙 y) h).hom.app F ≫
      (D.leftIdIso y).hom.app ((D.left p).obj F) = 𝟙 _ := by
    simp only [AdjunctionData.triangleIso, Iso.trans_hom, NatTrans.comp_app,
      eqToIso.hom, eqToHom_app]
    change (e ≫ (D.leftCompIso p (𝟙 y)).hom.app F) ≫
      (D.leftIdIso y).hom.app ((D.left p).obj F) = 𝟙 _
    exact (Category.assoc _ _ _).trans
      (ht.trans (by simp only [e, eqToHom_trans, eqToHom_refl]))
  simpa only [eqToIso_refl, Iso.refl_trans, Iso.hom_inv_id_app] using hT.symm

include hD in
/-- Fixed-source inverse triangles retain the original composite and transport. -/
theorem fixedSourceTriangle_comp {x y z t : J}
    (f : x ⟶ y) (g : x ⟶ z) (k : x ⟶ t) (a : y ⟶ z) (b : z ⟶ t)
    (d : y ⟶ t) (hd : d = a ≫ b)
    (ha : f ≫ a = g) (hb : g ≫ b = k) (hk : f ≫ d = k) (F : A x) :
    (D.triangleIso k f d hk).inv.app F =
      (eqToIso (congrArg D.left hd) ≪≫ D.leftCompIso a b).hom.app ((D.left f).obj F) ≫
        (D.left b).map ((D.triangleIso g f a ha).inv.app F) ≫
          (D.triangleIso k g b hb).inv.app F := by
  cases hd
  apply (cancel_epi ((D.triangleIso k f (a ≫ b) hk).hom.app F)).mp
  have ht := D.triangle_fixed_coefficient hD f g k a (a ≫ b) b ha hk hb rfl F
  have hi : (D.triangleIso (a ≫ b) a b rfl).hom.app ((D.left f).obj F) =
      (D.leftCompIso a b).hom.app ((D.left f).obj F) := by
    simp only [AdjunctionData.triangleIso, Iso.trans_hom, eqToIso.hom,
      eqToHom_refl, Category.id_comp]
  dsimp only [AdjunctionData.triangleCoefficientMap] at ht
  rw [hi] at ht
  have ht' : (D.triangleIso k f (a ≫ b) hk).hom.app F ≫
      (D.leftCompIso a b).hom.app ((D.left f).obj F) ≫
        (D.left b).map ((D.triangleIso g f a ha).inv.app F) =
      (D.triangleIso k g b hb).hom.app F := ht
  have hfinal := congrArg (fun z => z ≫ (D.triangleIso k g b hb).inv.app F) ht'
  simpa only [eqToIso_refl, Iso.refl_trans, Category.assoc, Iso.hom_inv_id_app] using hfinal.symm

variable (b : Cone X) (F : A b.pt)

/-- The transition on the original fixed-source coefficient, with no constant system model. -/
def System.fixedSourceTransition {i j : I} (a : i ⟶ j) :
    (D.left (X.map a)).obj ((D.left (b.π.app i)).obj F) ⟶
      (D.left (b.π.app j)).obj F :=
  (D.triangleIso (b.π.app j) (b.π.app i) (X.map a) (b.w a)).inv.app F

include hD in
/-- Fixed-source transitions satisfy the actual reindexed identity comparison. -/
theorem System.fixedSourceTransition_id (i : I) :
    fixedSourceTransition D X b F (𝟙 i) =
      ((D.reindex X).leftIdIso i).hom.app ((D.left (b.π.app i)).obj F) := by
  rw [D.leftIdIso_reindex X i]
  exact fixedSourceTriangle_id D hD (b.π.app i) (X.map (𝟙 i)) (X.map_id i) (b.w (𝟙 i)) F

include hD in
/-- Fixed-source transitions satisfy the actual reindexed composition comparison. -/
theorem System.fixedSourceTransition_comp {i j k : I} (a : i ⟶ j) (c : j ⟶ k) :
    fixedSourceTransition D X b F (a ≫ c) =
      ((D.reindex X).leftCompIso a c).hom.app ((D.left (b.π.app i)).obj F) ≫
        (D.left (X.map c)).map (fixedSourceTransition D X b F a) ≫
          fixedSourceTransition D X b F c := by
  rw [D.leftCompIso_reindex X a c]
  exact fixedSourceTriangle_comp D hD (b.π.app i) (b.π.app j) (b.π.app k)
    (X.map a) (X.map c) (X.map (a ≫ c)) (X.map_comp a c) (b.w a) (b.w c) (b.w (a ≫ c)) F

include hD in
/-- One fixed original coefficient and cone give the actual compatible system. -/
def System.fixedSource : System (D.reindex X) :=
  System.ofLeft (D.reindex X) (fun i => (D.left (b.π.app i)).obj F)
    (System.fixedSourceTransition D X b F)
    (System.fixedSourceTransition_id D X hD b F)
    (fun a c => System.fixedSourceTransition_comp D X hD b F a c)

/-- Recover the original inverse triangle on the actual fixed-source system. -/
@[simp]
theorem System.fixedSource_leftMap {i j : I} (a : i ⟶ j) :
    (System.fixedSource D X hD b F).leftMap (D.reindex X) a =
      System.fixedSourceTransition D X b F a :=
  System.ofLeft_leftMap (D.reindex X) (fun i => (D.left (b.π.app i)).obj F)
    (System.fixedSourceTransition D X b F)
    (System.fixedSourceTransition_id D X hD b F)
    (fun a c => System.fixedSourceTransition_comp D X hD b F a c) a

end FixedSource

end CategoryTheory.InjectiveSystem
