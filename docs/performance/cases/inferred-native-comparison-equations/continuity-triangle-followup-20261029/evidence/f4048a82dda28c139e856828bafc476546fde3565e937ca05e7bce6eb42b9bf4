/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackEtaleNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramLimitCoefficients
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.ConeExtension

/-! # Relative global sections after changing the fixed base -/
@[expose] public noncomputable section
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge

/-- The relative triangle square in the original functor category, before evaluation. -/
theorem inverseImageComp_triangle_whole {X S Y Z : Scheme.{u}} (f : S ⟶ X)
    (b : Z ⟶ S) (c : Y ⟶ S) (a : Y ⟶ Z) (e : a ≫ b = c) :
    (inverseImageComp f c).hom ≫
        Functor.whiskerLeft (inverseImage f) (pullbackTriangleIso c b a e).hom =
      (pullbackTriangleIso (c ≫ f) (b ≫ f) a
        (by rw [← Category.assoc, e])).hom ≫
        Functor.whiskerRight (inverseImageComp f b).hom (inverseImage a) ≫
        (Functor.associator (inverseImage f) (inverseImage b) (inverseImage a)).hom := by
  have hw := schemeAdjunctionData.triangleIso_precompose_whole schemeAdjunctionData_coherent
    f.op b.op c.op a.op (congrArg Quiver.Hom.op e)
  simp only [schemeTriangleIso_eq_pullbackTriangleIso,
    schemeLeftCompIso_eq_inverseImageComp, schemeLeft_eq_inverseImage,
    unop_comp, Quiver.Hom.unop_op] at hw ⊢
  exact hw

/-- Native coefficient composition respects a relative triangle over a fixed base. -/
theorem inverseImageComp_triangle {X S Y Z : Scheme.{u}} (f : S ⟶ X)
    (b : Z ⟶ S) (c : Y ⟶ S) (a : Y ⟶ Z) (e : a ≫ b = c)
    (F : AbelianSheaf.{u, u + 1} X) :
    (inverseImageComp f c).hom.app F ≫
        (pullbackTriangleIso c b a e).hom.app ((inverseImage f).obj F) =
      (pullbackTriangleIso (c ≫ f) (b ≫ f) a
        (by rw [← Category.assoc, e])).hom.app F ≫
        (inverseImage a).map ((inverseImageComp f b).hom.app F) := by
  have h := NatTrans.congr_app (inverseImageComp_triangle_whole f b c a e) F
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id] at h ⊢
  exact h

/-- Inverse triangle square at the original functor-category boundary. -/
theorem inverseImageComp_triangle_inv_whole {X S Y Z : Scheme.{u}} (f : S ⟶ X)
    (b : Z ⟶ S) (c : Y ⟶ S) (a : Y ⟶ Z) (e : a ≫ b = c) :
    (pullbackTriangleIso (c ≫ f) (b ≫ f) a
        (by rw [← Category.assoc, e])).inv ≫ (inverseImageComp f c).hom =
      (Functor.whiskerRight (inverseImageComp f b).hom (inverseImage a) ≫
        (Functor.associator (inverseImage f) (inverseImage b) (inverseImage a)).hom) ≫
        Functor.whiskerLeft (inverseImage f) (pullbackTriangleIso c b a e).inv := by
  have hw := schemeAdjunctionData.triangleIso_precompose_inv_whole
    schemeAdjunctionData_coherent f.op b.op c.op a.op (congrArg Quiver.Hom.op e)
  simp only [schemeTriangleIso_eq_pullbackTriangleIso,
    schemeLeftCompIso_eq_inverseImageComp, schemeLeft_eq_inverseImage,
    unop_comp, Quiver.Hom.unop_op] at hw ⊢
  exact hw

/-- The inverse form of the original relative coefficient square. -/
theorem inverseImageComp_triangle_inv {X S Y Z : Scheme.{u}} (f : S ⟶ X)
    (b : Z ⟶ S) (c : Y ⟶ S) (a : Y ⟶ Z) (e : a ≫ b = c)
    (F : AbelianSheaf.{u, u + 1} X) :
    (pullbackTriangleIso (c ≫ f) (b ≫ f) a
        (by rw [← Category.assoc, e])).inv.app F ≫
        (inverseImageComp f c).hom.app F =
      (inverseImage a).map ((inverseImageComp f b).hom.app F) ≫
        (pullbackTriangleIso c b a e).inv.app ((inverseImage f).obj F) := by
  have h := congrArg (fun t => t.app F) (inverseImageComp_triangle_inv_whole f b c a e)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id] using h

/-- The original section square, retained as a whole natural transformation. -/
theorem pullbackSections_base_whole {X S Y Z : Scheme.{u}} (f : S ⟶ X)
    (b : Z ⟶ S) (c : Y ⟶ S) (a : Y ⟶ Z) (e : a ≫ b = c) :
    (Functor.whiskerLeft (inverseImage (b ≫ f)) (globalSectionsPullbackNatTrans a) ≫
      Functor.whiskerRight (pullbackTriangleIso (c ≫ f) (b ≫ f) a
        (by rw [← Category.assoc, e])).inv (globalSections Y)) ≫
        Functor.whiskerRight (inverseImageComp f c).hom (globalSections Y) =
      Functor.whiskerRight (inverseImageComp f b).hom (globalSections Z) ≫
        Functor.whiskerLeft (inverseImage f ⋙ inverseImage b)
          (globalSectionsPullbackNatTrans a) ≫
        Functor.whiskerRight (Functor.whiskerLeft (inverseImage f)
          (pullbackTriangleIso c b a e).inv) (globalSections Y) := by
  have hw := schemeAdjunctionData.triangleIso_precompose_sections_whole
    schemeAdjunctionData_coherent f.op b.op c.op a.op (congrArg Quiver.Hom.op e)
    (globalSections Z) (globalSections Y) (globalSectionsPullbackNatTrans a)
  simp only [schemeTriangleIso_eq_pullbackTriangleIso,
    schemeLeftCompIso_eq_inverseImageComp, schemeLeft_eq_inverseImage,
    unop_comp, Quiver.Hom.unop_op] at hw ⊢
  exact hw

/-- Evaluate the whole section square without rebuilding its original functors. -/
theorem pullbackSections_base_app {X S Y Z : Scheme.{u}} (f : S ⟶ X)
    (b : Z ⟶ S) (c : Y ⟶ S) (a : Y ⟶ Z) (e : a ≫ b = c)
    (F : AbelianSheaf.{u, u + 1} X) :
    (globalSectionsPullback a ((inverseImage (b ≫ f)).obj F) ≫
      (globalSections Y).map ((pullbackTriangleIso (c ≫ f) (b ≫ f) a
        (by rw [← Category.assoc, e])).inv.app F)) ≫
        (globalSections Y).map ((inverseImageComp f c).hom.app F) =
      (globalSections Z).map ((inverseImageComp f b).hom.app F) ≫
        globalSectionsPullback a ((inverseImage b).obj ((inverseImage f).obj F)) ≫
        (globalSections Y).map
          ((pullbackTriangleIso c b a e).inv.app ((inverseImage f).obj F)) :=
  NatTrans.congr_app (pullbackSections_base_whole f b c a e) F

/-- The original relative section functor before evaluating its coefficient.
Its maps are the original unit followed by the original triangle comparison. -/
def pullbackSectionsBifunctor (X : Scheme.{u}) :
    (Over X)ᵒᵖ ⥤ AbelianSheaf.{u, u + 1} X ⥤ Ab.{u + 1} where
  obj U := inverseImage U.unop.hom ⋙ globalSections U.unop.left
  map {U V} a :=
    Functor.whiskerLeft (inverseImage U.unop.hom)
      (globalSectionsPullbackNatTrans a.unop.left) ≫
        Functor.whiskerRight
          (pullbackTriangleIso V.unop.hom U.unop.hom a.unop.left (Over.w a.unop)).inv
          (globalSections V.unop.left)
  map_id U := by
    apply NatTrans.ext
    funext F
    exact pullbackSectionsMap_id F U.unop
  map_comp a b := by
    apply NatTrans.ext
    funext F
    exact pullbackSectionsMap_comp F b.unop a.unop

/-- Evaluating the whole native section functor gives exactly the original functor. -/
def pullbackSectionsBifunctorEvaluationIso (X : Scheme.{u})
    (F : AbelianSheaf.{u, u + 1} X) :
    pullbackSectionsBifunctor X ⋙
        (CategoryTheory.evaluation (AbelianSheaf.{u, u + 1} X) Ab.{u + 1}).obj F ≅
      pullbackSectionsFunctor F := Iso.refl _

/-- Changing the fixed base at the whole coefficient-functor boundary. -/
def pullbackSectionsBaseBifunctorIso {X S : Scheme.{u}} (f : S ⟶ X) :
    (Over.map f).op ⋙ pullbackSectionsBifunctor X ≅
      pullbackSectionsBifunctor S ⋙
        (Functor.whiskeringLeft (AbelianSheaf.{u, u + 1} X)
          (AbelianSheaf.{u, u + 1} S) Ab.{u + 1}).obj (inverseImage f) :=
  NatIso.ofComponents
    (fun U ↦ Functor.isoWhiskerRight (inverseImageComp f U.unop.hom)
      (globalSections U.unop.left)) (by
    intro U V a
    change
      (Functor.whiskerLeft (inverseImage (U.unop.hom ≫ f))
          (globalSectionsPullbackNatTrans a.unop.left) ≫
        Functor.whiskerRight
          (pullbackTriangleIso (V.unop.hom ≫ f) (U.unop.hom ≫ f) a.unop.left
            (by rw [← Category.assoc, Over.w a.unop])).inv (globalSections V.unop.left)) ≫
          Functor.whiskerRight (inverseImageComp f V.unop.hom).hom
            (globalSections V.unop.left) =
        Functor.whiskerRight (inverseImageComp f U.unop.hom).hom
          (globalSections U.unop.left) ≫
            (Functor.whiskerLeft (inverseImage f ⋙ inverseImage U.unop.hom)
              (globalSectionsPullbackNatTrans a.unop.left) ≫
            Functor.whiskerRight (Functor.whiskerLeft (inverseImage f)
              (pullbackTriangleIso V.unop.hom U.unop.hom a.unop.left
                (Over.w a.unop)).inv) (globalSections V.unop.left))
    exact pullbackSections_base_whole f U.unop.hom V.unop.hom a.unop.left
      (Over.w a.unop))

/-- Changing the fixed base preserves the original relative section system.
The whole coefficient comparison is evaluated only after its native naturality proof. -/
def pullbackSectionsBaseIso {X S : Scheme.{u}} (f : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) :
    (Over.map f).op ⋙ pullbackSectionsFunctor F ≅
      pullbackSectionsFunctor ((inverseImage f).obj F) :=
  Functor.isoWhiskerLeft (Over.map f).op (pullbackSectionsBifunctorEvaluationIso X F).symm ≪≫
    (Functor.associator (Over.map f).op (pullbackSectionsBifunctor X)
      ((CategoryTheory.evaluation (AbelianSheaf.{u, u + 1} X) Ab.{u + 1}).obj F)).symm ≪≫
    Functor.isoWhiskerRight (pullbackSectionsBaseBifunctorIso f)
      ((CategoryTheory.evaluation (AbelianSheaf.{u, u + 1} X) Ab.{u + 1}).obj F) ≪≫
    pullbackSectionsBifunctorEvaluationIso S ((inverseImage f).obj F)

/-- On every fixed relative scheme, relative sections are the original pullback sheaf. -/
def pullbackSectionsBaseEtaleIso {X S : Scheme.{u}} (f : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) :
    (Scheme.Etale.forget S ⋙ Over.map f).op ⋙ pullbackSectionsFunctor F ≅
      ((inverseImage f).obj F).obj :=
  Functor.associator (Scheme.Etale.forget S).op (Over.map f).op
      (pullbackSectionsFunctor F) ≪≫
    Functor.isoWhiskerLeft (Scheme.Etale.forget S).op (pullbackSectionsBaseIso f F) ≪≫
    pullbackSectionsEtaleNatIso ((inverseImage f).obj F)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
