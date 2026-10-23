/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramPullbacks
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackCohomologySystem

/-! # Pulling compatible coefficients to a specified scheme cone -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge

/-- Transport of a coefficient transition to a fixed scheme, with its actual triangle. -/
def triangleCoefficientMap {Y Z T : Scheme.{u}} (f : Z ⟶ Y)
    (p : T ⟶ Y) (q : T ⟶ Z) (h : q ≫ f = p)
    {F : AbelianSheaf.{u, u + 1} Y} {G : AbelianSheaf.{u, u + 1} Z}
    (φ : (inverseImage f).obj F ⟶ G) :
    (inverseImage p).obj F ⟶ (inverseImage q).obj G :=
  (pullbackTriangleIso p f q h).hom.app F ≫ (inverseImage q).map φ

/-- Transporting two coefficient transitions composes by the original inverse-image comparison. -/
lemma triangleCoefficientMap_comp {Y Z W T : Scheme.{u}}
    (f : Z ⟶ Y) (g : W ⟶ Z) (p : T ⟶ Y) (q : T ⟶ Z) (r : T ⟶ W)
    (hp : q ≫ f = p) (hq : r ≫ g = q)
    {F : AbelianSheaf.{u, u + 1} Y} {G : AbelianSheaf.{u, u + 1} Z}
    {H : AbelianSheaf.{u, u + 1} W}
    (φ : (inverseImage f).obj F ⟶ G) (ψ : (inverseImage g).obj G ⟶ H) :
    triangleCoefficientMap f p q hp φ ≫ triangleCoefficientMap g q r hq ψ =
      triangleCoefficientMap (g ≫ f) p r (by rw [← Category.assoc, hq, hp])
        ((inverseImageComp f g).hom.app F ≫ (inverseImage g).map φ ≫ ψ) := by
  subst p
  subst q
  have hn := (inverseImageComp g r).hom.naturality φ
  have ha := congrArg (fun α => α.app F) (inverseImageComp_assoc_hom f g r)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id] at ha
  dsimp only [triangleCoefficientMap, pullbackTriangleIso, Iso.trans_hom,
    NatTrans.comp_app, eqToIso.hom, eqToHom_app]
  simp only [eqToHom_refl, NatTrans.id_app, Category.id_comp, Functor.map_comp,
    Category.assoc]
  rw [← Category.assoc ((inverseImage (r ≫ g)).map φ), hn]
  have ht := congrArg
    (fun k : (inverseImage ((r ≫ g) ≫ f)).obj F ⟶
        (inverseImage r).obj ((inverseImage g).obj ((inverseImage f).obj F)) =>
      k ≫ (inverseImage r).map ((inverseImage g).map φ) ≫ (inverseImage r).map ψ) ha
  simpa only [Category.assoc, Functor.comp_map, eqToIso.hom] using ht

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
