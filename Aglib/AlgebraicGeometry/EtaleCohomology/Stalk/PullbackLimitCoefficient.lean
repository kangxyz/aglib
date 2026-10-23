/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackCoefficientSystem
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramLimitSections
public import Mathlib.CategoryTheory.Limits.Connected

/-! # The actual limit coefficient of a fixed pullback system -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe uJ vJ uC vC

namespace CategoryTheory.Limits

/-- The colimit of a diagram canonically isomorphic to a constant connected diagram. -/
def constantDiagramColimitIso {I : Type uJ} {C : Type uC}
    [Category.{vJ} I] [Category.{vC} C]
    [IsConnected I] {D : I ⥤ C} [HasColimit D] {A : C}
    (e : (Functor.const I).obj A ≅ D) : colimit D ≅ A :=
  HasColimit.isoOfNatIso e.symm ≪≫
    (colimit.isColimit ((Functor.const I).obj A)).coconePointUniqueUpToIso
      (isColimitConstCocone I A)

private theorem constantDiagramColimitIso_ι {I : Type uJ} {C : Type uC}
    [Category.{vJ} I] [Category.{vC} C]
    [IsConnected I] {D : I ⥤ C} [HasColimit D] {A : C}
    (e : (Functor.const I).obj A ≅ D) (i : I) :
    colimit.ι D i ≫ (constantDiagramColimitIso e).hom = e.inv.app i := by
  change colimit.ι D i ≫ (HasColimit.isoOfNatIso e.symm).hom ≫
    ((colimit.isColimit ((Functor.const I).obj A)).coconePointUniqueUpToIso
      (isColimitConstCocone I A)).hom = e.inv.app i
  rw [HasColimit.ι_isoOfNatIso_hom_assoc]
  have hc : colimit.ι ((Functor.const I).obj A) i ≫
      ((colimit.isColimit ((Functor.const I).obj A)).coconePointUniqueUpToIso
        (isColimitConstCocone I A)).hom = 𝟙 A :=
    colimit.comp_coconePointUniqueUpToIso_hom (isColimitConstCocone I A) i
  exact (congrArg (fun t => e.inv.app i ≫ t) hc).trans (Category.comp_id _)

end CategoryTheory.Limits

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
  subst p
  have hc := pullbackTriangleIso_comp f g k q a ha hq F
  have hc' := congrArg
    (fun t => t ≫ (inverseImage q).map ((pullbackTriangleIso g f a ha).inv.app F)) hc
  have ht' : (pullbackTriangleIso (q ≫ a) a q rfl).hom.app
      ((inverseImage f).obj F) =
        (inverseImageComp a q).hom.app ((inverseImage f).obj F) := by
    simp only [pullbackTriangleIso, Iso.trans_hom,
      eqToIso.hom, eqToHom_refl, Category.id_comp]
  dsimp only [triangleCoefficientMap]
  rw [ht']
  have hv : (pullbackTriangleIso k f (q ≫ a) hp).hom.app F ≫
      (inverseImageComp a q).hom.app ((inverseImage f).obj F) ≫
        (inverseImage q).map ((pullbackTriangleIso g f a ha).inv.app F) =
      (pullbackTriangleIso k g q hq).hom.app F ≫
        (inverseImage q).map (𝟙 ((inverseImage g).obj F)) := by
    simpa only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] using hc'
  exact hv.trans ((congrArg (fun t => (pullbackTriangleIso k g q hq).hom.app F ≫ t)
    ((inverseImage q).map_id ((inverseImage g).obj F))).trans (Category.comp_id _))


private theorem triangle_fixed_coefficient_nat {X Y Z T : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ X) (k : T ⟶ X)
    (a : Z ⟶ Y) (p : T ⟶ Y) (q : T ⟶ Z)
    (ha : a ≫ f = g) (hp : p ≫ f = k) (hq : q ≫ g = k) (ht : q ≫ a = p) :
    (pullbackTriangleIso k f p hp).hom ≫
      Functor.whiskerLeft (inverseImage f) (pullbackTriangleIso p a q ht).hom ≫
        (Functor.associator (inverseImage f) (inverseImage a) (inverseImage q)).inv ≫
          Functor.whiskerRight (pullbackTriangleIso g f a ha).inv (inverseImage q) =
      (pullbackTriangleIso k g q hq).hom := by
  apply NatTrans.ext
  funext F
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp, triangleCoefficientMap] using
      triangle_fixed_coefficient f g k a p q ha hp hq ht F

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
  have h := congrArg (fun t => t.app F) (fixed_coefficient_diagram_nat Y b c l hl a)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] at h
  exact h

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
  exact NatIso.ofComponents (pullbackConeCoefficientComponent Y b c l hl F)
    (fun {i j} a => (Category.id_comp
      (pullbackConeCoefficientComponent Y b c l hl F j).hom).trans
      ((congrArg (fun t => (pullbackConeCoefficientComponent Y b c l hl F i).hom ≫ t)
        (coneCoefficientMap_pullbackCoefficientSystem Y b c F a)).trans
          (pullbackConeCoefficientComponent_triangle Y b c l hl F a)).symm)

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
  exact constantDiagramColimitIso_ι (pullbackConeCoefficientIso Y b c l hl F) i

end Colimit

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
