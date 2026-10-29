/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap

/-! # Original pullback of sections on relative schemes

All section maps are the original adjunction-unit maps at the original terminal
étale objects. Identity and composition follow the original constant-sheaf
adjunction and inverse-image coherence, without an Ext realization in their proofs.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge

/-- Identity pullback of actual sections, with the native coefficient transport. -/
@[reassoc]
theorem globalSectionsPullback_id (X : Scheme.{u})
    (F : AbelianSheaf.{u, u + 1} X) :
    globalSectionsPullback (𝟙 X) F ≫
        (globalSections X).map ((inverseImageId X).hom.app F) = 𝟙 _ := by
  let A : AddCommGrpCat.{u + 1} := (globalSections X).obj F
  let a : (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A ⟶ F :=
    (constantAdjunction X).counit.app F
  have ha : (constantAdjunction X).homEquiv A F a = 𝟙 A := by
    rw [Adjunction.homEquiv_unit]
    exact (constantAdjunction X).right_triangle_components F
  have h : (constantAdjunction X).homEquiv A ((inverseImage (𝟙 X)).obj F)
      (((inverseImageConstantIso (𝟙 X)).app A).inv ≫ (inverseImage (𝟙 X)).map a) =
      globalSectionsPullback (𝟙 X) F :=
    (constantTransport_homEquiv (𝟙 X) A (L := F) a).trans
      ((congrArg (fun b : A ⟶ A => b ≫ globalSectionsPullback (𝟙 X) F) ha).trans
        (Category.id_comp _))
  have hi :
      (((inverseImageConstantIso (𝟙 X)).app A).inv ≫
        (inverseImage (𝟙 X)).map a) ≫ (inverseImageId X).hom.app F = a := by
    rw [Category.assoc, (inverseImageId X).hom.naturality a, inverseImageId_constant]
    dsimp only [Functor.id_obj]
    simpa only [Functor.id_map, Iso.app_hom, Iso.app_inv] using
      ((inverseImageConstantIso (𝟙 X)).app A).inv_hom_id_assoc a
  calc
    globalSectionsPullback (𝟙 X) F ≫
        (globalSections X).map ((inverseImageId X).hom.app F) =
      (constantAdjunction X).homEquiv A F
        ((((inverseImageConstantIso (𝟙 X)).app A).inv ≫
          (inverseImage (𝟙 X)).map a) ≫ (inverseImageId X).hom.app F) := by
      exact (((constantAdjunction X).homEquiv_naturality_right
        (((inverseImageConstantIso (𝟙 X)).app A).inv ≫ (inverseImage (𝟙 X)).map a)
        ((inverseImageId X).hom.app F)).trans
          (congrArg (fun b : A ⟶ (globalSections X).obj ((inverseImage (𝟙 X)).obj F) =>
            b ≫ (globalSections X).map ((inverseImageId X).hom.app F)) h)).symm
    _ = (constantAdjunction X).homEquiv A F a :=
      congrArg ((constantAdjunction X).homEquiv A F) hi
    _ = 𝟙 A := ha

/-- Composition of actual section pullbacks, with the original inverse-image comparison. -/
@[reassoc]
theorem globalSectionsPullback_comp {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (F : AbelianSheaf.{u, u + 1} X) :
    globalSectionsPullback (g ≫ f) F ≫
        (globalSections T).map ((inverseImageComp f g).hom.app F) =
      globalSectionsPullback f F ≫ globalSectionsPullback g ((inverseImage f).obj F) := by
  let A : AddCommGrpCat.{u + 1} := (globalSections X).obj F
  let a : (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A ⟶ F :=
    (constantAdjunction X).counit.app F
  have ha : (constantAdjunction X).homEquiv A F a = 𝟙 A := by
    rw [Adjunction.homEquiv_unit]
    exact (constantAdjunction X).right_triangle_components F
  have hf : (constantAdjunction S).homEquiv A ((inverseImage f).obj F)
      (((inverseImageConstantIso f).app A).inv ≫ (inverseImage f).map a) =
      globalSectionsPullback f F :=
    (constantTransport_homEquiv f A (L := F) a).trans
      ((congrArg (fun b : A ⟶ A => b ≫ globalSectionsPullback f F) ha).trans
        (Category.id_comp _))
  have hgf : (constantAdjunction T).homEquiv A ((inverseImage (g ≫ f)).obj F)
      (((inverseImageConstantIso (g ≫ f)).app A).inv ≫ (inverseImage (g ≫ f)).map a) =
      globalSectionsPullback (g ≫ f) F :=
    (constantTransport_homEquiv (g ≫ f) A (L := F) a).trans
      ((congrArg (fun b : A ⟶ A => b ≫ globalSectionsPullback (g ≫ f) F) ha).trans
        (Category.id_comp _))
  have hg : (constantAdjunction T).homEquiv A ((inverseImage g).obj ((inverseImage f).obj F))
      (((inverseImageConstantIso g).app A).inv ≫ (inverseImage g).map
        (((inverseImageConstantIso f).app A).inv ≫ (inverseImage f).map a)) =
      (constantAdjunction S).homEquiv A ((inverseImage f).obj F)
          (((inverseImageConstantIso f).app A).inv ≫ (inverseImage f).map a) ≫
        globalSectionsPullback g ((inverseImage f).obj F) :=
    constantTransport_homEquiv g A (L := (inverseImage f).obj F)
      (((inverseImageConstantIso f).app A).inv ≫ (inverseImage f).map a)
  have hc :
      (((inverseImageConstantIso (g ≫ f)).app A).inv ≫
        (inverseImage (g ≫ f)).map a) ≫ (inverseImageComp f g).hom.app F =
      ((inverseImageConstantIso g).app A).inv ≫
        (inverseImage g).map
          (((inverseImageConstantIso f).app A).inv ≫ (inverseImage f).map a) := by
    calc
      _ = ((inverseImageConstantIso (g ≫ f)).app A).inv ≫
          (inverseImageComp f g).hom.app
            ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A) ≫
          (inverseImage g).map ((inverseImage f).map a) := by
        simpa only [Category.assoc, Functor.comp_map] using
          congrArg (fun q => ((inverseImageConstantIso (g ≫ f)).app A).inv ≫ q)
            ((inverseImageComp f g).hom.naturality a)
      _ = (((inverseImageConstantIso g).app A).inv ≫
          (inverseImage g).map ((inverseImageConstantIso f).inv.app A)) ≫
          (inverseImage g).map ((inverseImage f).map a) := by
        simpa only [Category.assoc, Iso.app_inv] using
          congrArg (fun q => q ≫ (inverseImage g).map ((inverseImage f).map a))
            (inverseImageComp_constant_inv f g A)
      _ = _ := by simp only [Functor.map_comp, Category.assoc, Iso.app_inv]
  calc
    globalSectionsPullback (g ≫ f) F ≫
        (globalSections T).map ((inverseImageComp f g).hom.app F) =
      (constantAdjunction T).homEquiv A _
        ((((inverseImageConstantIso (g ≫ f)).app A).inv ≫
          (inverseImage (g ≫ f)).map a) ≫ (inverseImageComp f g).hom.app F) := by
      exact (((constantAdjunction T).homEquiv_naturality_right
        (((inverseImageConstantIso (g ≫ f)).app A).inv ≫ (inverseImage (g ≫ f)).map a)
        ((inverseImageComp f g).hom.app F)).trans
          (congrArg (fun b : A ⟶ (globalSections T).obj ((inverseImage (g ≫ f)).obj F) =>
            b ≫ (globalSections T).map ((inverseImageComp f g).hom.app F)) hgf)).symm
    _ = (constantAdjunction T).homEquiv A _
        (((inverseImageConstantIso g).app A).inv ≫
          (inverseImage g).map
            (((inverseImageConstantIso f).app A).inv ≫ (inverseImage f).map a)) :=
      congrArg ((constantAdjunction T).homEquiv A
        ((inverseImage g).obj ((inverseImage f).obj F))) hc
    _ = globalSectionsPullback f F ≫
        globalSectionsPullback g ((inverseImage f).obj F) := by
      exact hg.trans (congrArg
        (fun b : A ⟶ (globalSections S).obj ((inverseImage f).obj F) =>
          b ≫ globalSectionsPullback g ((inverseImage f).obj F)) hf)

/-- Native inverse-image identification attached to a commuting triangle. -/
def pullbackTriangleIso {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X)
    (a : Y ⟶ Z) (h : a ≫ g = f) :
    inverseImage f ≅ inverseImage g ⋙ inverseImage a :=
  eqToIso (congrArg (fun k : Y ⟶ X => inverseImage k) h.symm) ≪≫ inverseImageComp g a

/-- Composition of the original triangle identifications. -/
@[reassoc]
theorem pullbackTriangleIso_comp {X Y Z W : Scheme.{u}}
    (f : W ⟶ X) (g : Z ⟶ X) (h : Y ⟶ X) (a : Y ⟶ Z) (b : Z ⟶ W)
    (hb : b ≫ f = g) (ha : a ≫ g = h) (F : AbelianSheaf.{u, u + 1} X) :
    (pullbackTriangleIso h f (a ≫ b) (by rw [Category.assoc, hb, ha])).hom.app F ≫
        (inverseImageComp b a).hom.app ((inverseImage f).obj F) =
      (pullbackTriangleIso h g a ha).hom.app F ≫
        (inverseImage a).map ((pullbackTriangleIso g f b hb).hom.app F) := by
  subst g
  subst h
  have hc := congrArg (fun α => α.app F) (inverseImageComp_assoc_hom f b a)
  apply (cancel_epi (eqToHom (congrArg (fun k : Y ⟶ X => (inverseImage k).obj F)
    (Category.assoc a b f)))).1
  simpa only [pullbackTriangleIso, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
    eqToHom_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id, Category.assoc,
    eqToHom_refl, Category.id_comp, eqToHom_trans_assoc, eqToHom_trans] using hc

/-- The identity triangle uses exactly the original inverse-image identity. -/
theorem pullbackTriangleIso_id {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) :
    (pullbackTriangleIso f f (𝟙 Y) (Category.id_comp f)).hom.app F =
      (inverseImageId Y).inv.app ((inverseImage f).obj F) := by
  apply (cancel_mono ((inverseImageId Y).hom.app ((inverseImage f).obj F))).1
  have hc := congrArg (fun e => e.hom.app F) (inverseImageComp_comp_id f)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    eqToIso.hom, eqToHom_app] at hc
  simpa only [pullbackTriangleIso, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app, Category.assoc, hc, eqToHom_trans, eqToHom_refl,
    Iso.inv_hom_id_app]

/-- Inverse form of the native triangle composition law. -/
@[reassoc]
theorem pullbackTriangleIso_comp_inv {X Y Z W : Scheme.{u}}
    (f : W ⟶ X) (g : Z ⟶ X) (h : Y ⟶ X) (a : Y ⟶ Z) (b : Z ⟶ W)
    (hb : b ≫ f = g) (ha : a ≫ g = h) (F : AbelianSheaf.{u, u + 1} X) :
    (inverseImageComp b a).hom.app ((inverseImage f).obj F) ≫
        (inverseImage a).map ((pullbackTriangleIso g f b hb).inv.app F) ≫
        (pullbackTriangleIso h g a ha).inv.app F =
      (pullbackTriangleIso h f (a ≫ b) (by rw [Category.assoc, hb, ha])).inv.app F := by
  apply (cancel_epi
    ((pullbackTriangleIso h f (a ≫ b) (by rw [Category.assoc, hb, ha])).hom.app F)).1
  rw [← Category.assoc, pullbackTriangleIso_comp f g h a b hb ha F]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  have hm := (inverseImage a).map_id ((inverseImage g).obj F)
  exact (congrArg (fun k =>
    (pullbackTriangleIso h g a ha).hom.app F ≫ k ≫
      (pullbackTriangleIso h g a ha).inv.app F) hm).trans
    ((congrArg (fun k => (pullbackTriangleIso h g a ha).hom.app F ≫ k)
      (Category.id_comp ((pullbackTriangleIso h g a ha).inv.app F))).trans
        ((pullbackTriangleIso h g a ha).hom_inv_id_app F))

namespace Continuity

/-- Section transport along a relative scheme morphism, using the original unit. -/
def pullbackSectionsMap {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X)
    {Y Z : Over X} (a : Y ⟶ Z) :
    (globalSections Z.left).obj ((inverseImage Z.hom).obj F) ⟶
      (globalSections Y.left).obj ((inverseImage Y.hom).obj F) :=
  globalSectionsPullback a.left ((inverseImage Z.hom).obj F) ≫
    (globalSections Y.left).map
      ((pullbackTriangleIso Y.hom Z.hom a.left (Over.w a)).inv.app F)

@[simp]
theorem pullbackSectionsMap_id {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X)
    (Y : Over X) : pullbackSectionsMap F (𝟙 Y) = 𝟙 _ := by
  have h := pullbackTriangleIso_id Y.hom F
  have hi : (pullbackTriangleIso Y.hom Y.hom (𝟙 Y.left) (Category.id_comp Y.hom)).inv.app F =
      (inverseImageId Y.left).hom.app ((inverseImage Y.hom).obj F) := by
    apply (cancel_epi ((pullbackTriangleIso Y.hom Y.hom (𝟙 Y.left)
      (Category.id_comp Y.hom)).hom.app F)).1
    rw [Iso.hom_inv_id_app, h, Iso.inv_hom_id_app]
    rfl
  change globalSectionsPullback (𝟙 Y.left) ((inverseImage Y.hom).obj F) ≫
    (globalSections Y.left).map
      ((pullbackTriangleIso Y.hom Y.hom (𝟙 Y.left) (Category.id_comp Y.hom)).inv.app F) = _
  rw [hi, globalSectionsPullback_id]

@[reassoc]
theorem pullbackSectionsMap_comp {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X)
    {Y Z W : Over X} (a : Y ⟶ Z) (b : Z ⟶ W) :
    pullbackSectionsMap F (a ≫ b) = pullbackSectionsMap F b ≫ pullbackSectionsMap F a := by
  dsimp only [pullbackSectionsMap]
  simp only [Category.assoc]
  rw [globalSectionsPullback_naturality_assoc,
    ← globalSectionsPullback_comp_assoc]
  simp only [← Functor.map_comp, pullbackTriangleIso_comp_inv, Over.comp_left]

/-- Original relative section transport is natural in the coefficient. -/
@[reassoc]
theorem pullbackSectionsMap_naturality {X : Scheme.{u}}
    {F G : AbelianSheaf.{u, u + 1} X} (q : F ⟶ G) {Y Z : Over X} (a : Y ⟶ Z) :
    (globalSections Z.left).map ((inverseImage Z.hom).map q) ≫ pullbackSectionsMap G a =
      pullbackSectionsMap F a ≫ (globalSections Y.left).map ((inverseImage Y.hom).map q) := by
  have h : (inverseImage a.left).map ((inverseImage Z.hom).map q) ≫
      (pullbackTriangleIso Y.hom Z.hom a.left (Over.w a)).inv.app G =
    (pullbackTriangleIso Y.hom Z.hom a.left (Over.w a)).inv.app F ≫
      (inverseImage Y.hom).map q :=
    (pullbackTriangleIso Y.hom Z.hom a.left (Over.w a)).inv.naturality q
  dsimp only [pullbackSectionsMap]
  rw [← Category.assoc, globalSectionsPullback_naturality]
  simp only [Category.assoc, ← Functor.map_comp, h]

/-- Original sections of pullbacks form a contravariant functor on relative schemes. -/
def pullbackSectionsFunctor {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X) :
    (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj Y := (globalSections Y.unop.left).obj ((inverseImage Y.unop.hom).obj F)
  map a := pullbackSectionsMap F a.unop
  map_id Y := pullbackSectionsMap_id F Y.unop
  map_comp a b := pullbackSectionsMap_comp F b.unop a.unop

/-- The canonical coefficient transformation between relative section functors. -/
def pullbackSectionsNatTrans {X : Scheme.{u}} {F G : AbelianSheaf.{u, u + 1} X}
    (q : F ⟶ G) : pullbackSectionsFunctor F ⟶ pullbackSectionsFunctor G where
  app Y := (globalSections Y.unop.left).map ((inverseImage Y.unop.hom).map q)
  naturality _ _ a := (pullbackSectionsMap_naturality q a.unop).symm

/-- The original cone projections give the canonical cocone on pullback sections. -/
def pullbackSectionsCocone {X : Scheme.{u}} {I : Type*} [Category I]
    (D : I ⥤ Over X) (c : Cone D) (F : AbelianSheaf.{u, u + 1} X) :
    Cocone (D.op ⋙ pullbackSectionsFunctor F) :=
  (pullbackSectionsFunctor F).mapCocone c.op

@[simp]
theorem pullbackSectionsCocone_ι {X : Scheme.{u}} {I : Type*} [Category I]
    (D : I ⥤ Over X) (c : Cone D) (F : AbelianSheaf.{u, u + 1} X) (i : I) :
    (pullbackSectionsCocone D c F).ι.app (op i) = pullbackSectionsMap F (c.π.app i) := rfl

end Continuity

end AlgebraicGeometry.Scheme.EtaleCohomology
