/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackCoefficientSystem
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramLimitSections
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.ConeConstancy

/-! # The actual limit coefficient of a fixed pullback system -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk

universe u uI vI
attribute [local instance] hasSheafifyLarge
open Continuity

private theorem triangle_fixed_coefficient {X Y Z T : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ X) (k : T ⟶ X)
    (a : Z ⟶ Y) (p : T ⟶ Y) (q : T ⟶ Z)
    (ha : a ≫ f = g) (hp : p ≫ f = k) (hq : q ≫ g = k) (ht : q ≫ a = p)
    (F : AbelianSheaf.{u, u + 1} X) :
    (pullbackTriangleIso k f p hp).hom.app F ≫
        triangleCoefficientMap a p q ht ((pullbackTriangleIso g f a ha).inv.app F) =
      (pullbackTriangleIso k g q hq).hom.app F := by
  simpa only [InjectiveSystem.AdjunctionData.triangleCoefficientMap,
    schemeTriangleIso_eq_pullbackTriangleIso, schemeLeft_eq_inverseImage,
    triangleCoefficientMap, Quiver.Hom.unop_op] using
    schemeAdjunctionData.triangle_fixed_coefficient schemeAdjunctionData_coherent
      f.op g.op k.op a.op p.op q.op (congrArg Quiver.Hom.op ha)
      (congrArg Quiver.Hom.op hp) (congrArg Quiver.Hom.op hq) (congrArg Quiver.Hom.op ht) F


private theorem triangle_fixed_coefficient_nat {X Y Z T : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ X) (k : T ⟶ X)
    (a : Z ⟶ Y) (p : T ⟶ Y) (q : T ⟶ Z)
    (ha : a ≫ f = g) (hp : p ≫ f = k) (hq : q ≫ g = k) (ht : q ≫ a = p) :
    (pullbackTriangleIso k f p hp).hom ≫
      Functor.whiskerLeft (inverseImage f) (pullbackTriangleIso p a q ht).hom ≫
        (Functor.associator (inverseImage f) (inverseImage a) (inverseImage q)).inv ≫
          Functor.whiskerRight (pullbackTriangleIso g f a ha).inv (inverseImage q) =
      (pullbackTriangleIso k g q hq).hom := by
  simpa only [schemeTriangleIso_eq_pullbackTriangleIso, schemeLeft_eq_inverseImage,
    Quiver.Hom.unop_op] using
    schemeAdjunctionData.triangle_fixed_coefficient_nat schemeAdjunctionData_coherent
      f.op g.op k.op a.op p.op q.op (congrArg Quiver.Hom.op ha)
      (congrArg Quiver.Hom.op hp) (congrArg Quiver.Hom.op hq) (congrArg Quiver.Hom.op ht)

variable {I : Type uI} [Category.{vI} I] (Y : I ⥤ Scheme.{u}ᵒᵖ)
  (b : Cone Y) (c : Cocone Y) (l : b.pt ⟶ c.pt)
  (hl : ∀ i, b.π.app i ≫ c.ι.app i = l)
  (F : AbelianSheaf.{u, u + 1} b.pt.unop)

/-- The original triangle is an isomorphism with the exact native diagram endpoints. -/
def pullbackConeCoefficientComponent (i : I) :
    ((Functor.const I).obj ((inverseImage l.unop).obj F)).obj i ≅
      (coneCoefficientFunctor Y c (pullbackCoefficientSystem Y b F)).obj i :=
  (pullbackTriangleIso l.unop (b.π.app i).unop (c.ι.app i).unop
    (congrArg Quiver.Hom.unop (hl i))).app F

private theorem fixed_coefficient_diagram_nat {i j : I} (a : i ⟶ j) :
    (pullbackTriangleIso l.unop (b.π.app i).unop (c.ι.app i).unop
      (congrArg Quiver.Hom.unop (hl i))).hom ≫
        Functor.whiskerLeft (inverseImage (b.π.app i).unop)
          (pullbackTriangleIso (c.ι.app i).unop (Y.map a).unop (c.ι.app j).unop
            (congrArg Quiver.Hom.unop (c.w a))).hom ≫
        (Functor.associator (inverseImage (b.π.app i).unop)
          (inverseImage (Y.map a).unop) (inverseImage (c.ι.app j).unop)).inv ≫
        Functor.whiskerRight
          (pullbackTriangleIso (b.π.app j).unop (b.π.app i).unop (Y.map a).unop
            (congrArg Quiver.Hom.unop (b.w a))).inv (inverseImage (c.ι.app j).unop) =
      (pullbackTriangleIso l.unop (b.π.app j).unop (c.ι.app j).unop
        (congrArg Quiver.Hom.unop (hl j))).hom :=
  triangle_fixed_coefficient_nat (b.π.app i).unop (b.π.app j).unop l.unop
    (Y.map a).unop (c.ι.app i).unop (c.ι.app j).unop
    (congrArg Quiver.Hom.unop (b.w a)) (congrArg Quiver.Hom.unop (hl i))
    (congrArg Quiver.Hom.unop (hl j)) (congrArg Quiver.Hom.unop (c.w a))

/-- The original structural triangles commute with the actual fixed-coefficient transition. -/
theorem pullbackConeCoefficientComponent_triangle {i j : I} (a : i ⟶ j) :
    (pullbackConeCoefficientComponent Y b c l hl F i).hom ≫
        triangleCoefficientMap (Y.map a).unop (c.ι.app i).unop (c.ι.app j).unop
          (congrArg Quiver.Hom.unop (c.w a)) (pullbackCoefficientTransition Y b F a) =
      (pullbackConeCoefficientComponent Y b c l hl F j).hom := by
  exact triangle_fixed_coefficient (b.π.app i).unop (b.π.app j).unop l.unop
    (Y.map a).unop (c.ι.app i).unop (c.ι.app j).unop
    (congrArg Quiver.Hom.unop (b.w a)) (congrArg Quiver.Hom.unop (hl i))
    (congrArg Quiver.Hom.unop (hl j)) (congrArg Quiver.Hom.unop (c.w a)) F

/-- The native cone coefficient map retains the original fixed-sheaf triangle transition. -/
theorem coneCoefficientMap_pullbackCoefficientSystem {i j : I} (a : i ⟶ j) :
    coneCoefficientMap Y c (pullbackCoefficientSystem Y b F) a =
      triangleCoefficientMap (Y.map a).unop (c.ι.app i).unop (c.ι.app j).unop
        (congrArg Quiver.Hom.unop (c.w a)) (pullbackCoefficientTransition Y b F a) :=
  congrArg (triangleCoefficientMap (Y.map a).unop (c.ι.app i).unop (c.ι.app j).unop
    (congrArg Quiver.Hom.unop (c.w a)))
      (diagramInverseTransition_pullbackCoefficientSystem Y b F a)

include hl in
/-- The actual pulled-back coefficient diagram is canonically constant. -/
def pullbackConeCoefficientIso :
    (Functor.const I).obj ((inverseImage l.unop).obj F) ≅
      coneCoefficientFunctor Y c (pullbackCoefficientSystem Y b F) := by
  let C := coneCoefficientFunctor Y c (pullbackCoefficientSystem Y b F)
  let hobj : ∀ i, C.obj i =
      (schemeAdjunctionData.left (c.ι.app i)).obj
        ((schemeAdjunctionData.left (b.π.app i)).obj F) := fun _ => rfl
  apply schemeAdjunctionData.fixedCoefficientIso schemeAdjunctionData_coherent
    Y b c l hl F C hobj
  intro i j a
  change coneCoefficientMap Y c (pullbackCoefficientSystem Y b F) a =
    𝟙 _ ≫ schemeAdjunctionData.triangleCoefficientMap (Y.map a)
      (c.ι.app i) (c.ι.app j) (c.w a)
      ((schemeAdjunctionData.triangleIso (b.π.app j) (b.π.app i)
        (Y.map a) (b.w a)).inv.app F) ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id, coneCoefficientMap_pullbackCoefficientSystem]
  simp only [InjectiveSystem.AdjunctionData.triangleCoefficientMap,
    schemeTriangleIso_eq_pullbackTriangleIso, schemeLeft_eq_inverseImage, triangleCoefficientMap,
    pullbackCoefficientTransition]
  rfl

/-- The generic constancy isomorphism retains every original structural component. -/
theorem pullbackConeCoefficientIso_app (i : I) :
    (pullbackConeCoefficientIso Y b c l hl F).app i =
      pullbackConeCoefficientComponent Y b c l hl F i := by
  apply Iso.ext
  change (schemeAdjunctionData.triangleIso l (b.π.app i) (c.ι.app i) (hl i)).hom.app F ≫
      𝟙 _ =
    (pullbackTriangleIso l.unop (b.π.app i).unop (c.ι.app i).unop
      (congrArg Quiver.Hom.unop (hl i))).hom.app F
  simp only [schemeTriangleIso_eq_pullbackTriangleIso, Category.comp_id]

section Colimit

variable [IsConnected I]
  [HasColimit (coneCoefficientFunctor Y c (pullbackCoefficientSystem Y b F))]

include hl in
/-- The actual coefficient colimit is the original pullback of the fixed sheaf. -/
def pullbackLimitCoefficientIso :
    colimit (coneCoefficientFunctor Y c (pullbackCoefficientSystem Y b F)) ≅
      (inverseImage l.unop).obj F :=
  constantDiagramColimitIso (pullbackConeCoefficientIso Y b c l hl F)

/-- Each original coefficient insertion is precisely its structural triangle map. -/
@[reassoc]
theorem ι_pullbackLimitCoefficientIso_hom (i : I) :
    colimit.ι (coneCoefficientFunctor Y c (pullbackCoefficientSystem Y b F)) i ≫
        (pullbackLimitCoefficientIso Y b c l hl F).hom =
      (pullbackTriangleIso l.unop (b.π.app i).unop (c.ι.app i).unop
        (congrArg Quiver.Hom.unop (hl i))).inv.app F := by
  have hι :
      colimit.ι (coneCoefficientFunctor Y c (pullbackCoefficientSystem Y b F)) i ≫
          (pullbackLimitCoefficientIso Y b c l hl F).hom =
        (pullbackConeCoefficientComponent Y b c l hl F i).inv :=
    (constantDiagramColimitIso_ι (pullbackConeCoefficientIso Y b c l hl F) i).trans
      (congrArg Iso.inv (pullbackConeCoefficientIso_app Y b c l hl F i))
  exact hι

end Colimit

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
