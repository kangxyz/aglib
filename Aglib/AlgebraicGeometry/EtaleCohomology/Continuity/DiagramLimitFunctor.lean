/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramLimitCoefficients

/-! # The actual coefficient diagram at an inverse scheme cone -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge

/-- Transporting the identity coefficient through the original identity comparison is identity. -/
lemma triangleCoefficientMap_identity {Y T : Scheme.{u}} (f : Y ⟶ Y) (e : f = 𝟙 Y)
    (p : T ⟶ Y) (F : AbelianSheaf.{u, u + 1} Y) :
    triangleCoefficientMap f p p (by rw [e, Category.comp_id])
      (eqToHom (congrArg (fun k : Y ⟶ Y => (inverseImage k).obj F) e) ≫
        (inverseImageId Y).hom.app F) = 𝟙 ((inverseImage p).obj F) := by
  subst f
  have hc := congrArg (fun e => e.hom.app F) (inverseImageComp_id_comp p)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    eqToIso.hom, eqToHom_app] at hc
  change (inverseImageComp (𝟙 Y) p).hom.app F ≫
    (inverseImage p).map ((inverseImageId Y).hom.app F) ≫
      𝟙 ((inverseImage p).obj F) = eqToHom _ at hc
  let m : (inverseImage p).obj ((inverseImage (𝟙 Y)).obj F) ⟶
      (inverseImage p).obj F := (inverseImage p).map ((inverseImageId Y).hom.app F)
  have hc' : (inverseImageComp (𝟙 Y) p).hom.app F ≫ m =
      eqToHom (congrArg (fun k : T ⟶ Y => (inverseImage k).obj F)
        (Category.comp_id p)) :=
    (congrArg
      (fun k : (inverseImage p).obj ((inverseImage (𝟙 Y)).obj F) ⟶
          (inverseImage p).obj F => (inverseImageComp (𝟙 Y) p).hom.app F ≫ k)
      (Category.comp_id m)).symm.trans hc
  have ht := congrArg
    (fun k : (inverseImage (p ≫ 𝟙 Y)).obj F ⟶ (inverseImage p).obj F =>
      eqToHom (congrArg (fun t : T ⟶ Y => (inverseImage t).obj F)
        (Category.comp_id p).symm) ≫ k) hc'
  simpa only [triangleCoefficientMap, pullbackTriangleIso, Iso.trans_hom,
    NatTrans.comp_app, eqToIso.hom, eqToHom_app, eqToHom_refl,
    Category.id_comp, Category.assoc, eqToHom_trans, m] using ht

/-- The coefficient composition law retains a supplied equality of scheme maps. -/
lemma triangleCoefficientMap_comp_transport {Y Z W T : Scheme.{u}}
    (f : Z ⟶ Y) (g : W ⟶ Z) (t : W ⟶ Y) (e : t = g ≫ f)
    (p : T ⟶ Y) (q : T ⟶ Z) (r : T ⟶ W)
    (hp : q ≫ f = p) (hq : r ≫ g = q)
    {F : AbelianSheaf.{u, u + 1} Y} {G : AbelianSheaf.{u, u + 1} Z}
    {H : AbelianSheaf.{u, u + 1} W}
    (φ : (inverseImage f).obj F ⟶ G) (ψ : (inverseImage g).obj G ⟶ H) :
    triangleCoefficientMap f p q hp φ ≫ triangleCoefficientMap g q r hq ψ =
      triangleCoefficientMap t p r (by rw [e, ← Category.assoc, hq, hp])
        (eqToHom (congrArg (fun k : W ⟶ Y => (inverseImage k).obj F) e) ≫
          (inverseImageComp f g).hom.app F ≫ (inverseImage g).map φ ≫ ψ) := by
  subst t
  simpa only [eqToHom_refl, Category.id_comp] using
    triangleCoefficientMap_comp f g p q r hp hq φ ψ

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (c : Cocone X) (F : DiagramCoefficientSystem X)

/-- The coefficient at a stage pulled to the specified cone point. -/
abbrev coneCoefficientObj (i : I) : AbelianSheaf.{u, u + 1} c.pt.unop :=
  (inverseImage (c.ι.app i).unop).obj (F.obj i)

/-- The actual compatible transition at the cone point. -/
def coneCoefficientMap {i j : I} (a : i ⟶ j) :
    coneCoefficientObj X c F i ⟶ coneCoefficientObj X c F j :=
  triangleCoefficientMap (X.map a).unop (c.ι.app i).unop (c.ι.app j).unop
    (congrArg (fun k : X.obj i ⟶ c.pt => k.unop) (c.w a))
    (diagramInverseTransition X F a)

/-- The original coefficient system produces an actual diagram on the cone point. -/
def coneCoefficientFunctor : I ⥤ AbelianSheaf.{u, u + 1} c.pt.unop where
  obj := coneCoefficientObj X c F
  map := coneCoefficientMap X c F
  map_id i := by
    dsimp only [coneCoefficientMap]
    rw [diagramInverseTransition_id]
    simp only [diagramInverseImageId, Iso.trans_hom, NatTrans.comp_app,
      eqToIso.hom, eqToHom_app]
    exact triangleCoefficientMap_identity (X.map (𝟙 i)).unop
      (congrArg (fun k : X.obj i ⟶ X.obj i => k.unop) (X.map_id i))
      (c.ι.app i).unop (F.obj i)
  map_comp {i j k} a b := by
    dsimp only [coneCoefficientMap]
    rw [diagramInverseTransition_comp]
    simp only [diagramInverseImageComp, Iso.trans_hom, NatTrans.comp_app,
      eqToIso.hom, eqToHom_app]
    exact (triangleCoefficientMap_comp_transport (X.map a).unop (X.map b).unop
      (X.map (a ≫ b)).unop
      (congrArg (fun t : X.obj i ⟶ X.obj k => t.unop) (X.map_comp a b))
      (c.ι.app i).unop (c.ι.app j).unop (c.ι.app k).unop
      (congrArg (fun t : X.obj i ⟶ c.pt => t.unop) (c.w a))
      (congrArg (fun t : X.obj j ⟶ c.pt => t.unop) (c.w b))
      (diagramInverseTransition X F a) (diagramInverseTransition X F b)).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
