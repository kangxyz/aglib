/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramAdjointCocone

/-! # Native composition coherence of the cone direct-image triangles -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge

lemma directImageTriangleIso_comp {X Y Z T : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (p : T ⟶ X) (q : T ⟶ Y) (r : T ⟶ Z)
    (hp : q ≫ f = p) (hq : r ≫ g = q) (L : AbelianSheaf.{u, u + 1} T) :
    (directImageCompIso f g).hom.app ((directImage r).obj L) ≫
        (directImageTriangleIso (g ≫ f) p r
          (by rw [← Category.assoc, hq, hp])).hom.app L =
      (directImage f).map ((directImageTriangleIso g q r hq).hom.app L) ≫
        (directImageTriangleIso f p q hp).hom.app L := by
  subst p
  subst q
  have ht := congrArg (fun k => k ≫
    eqToHom (congrArg (fun s : T ⟶ X => (directImage s).obj L)
      (Category.assoc r g f).symm)) (directImageCompIso_assoc_app f g r L)
  have hc : (directImage f).map ((directImageCompIso g r).hom.app L) ≫
      (directImageCompIso f (r ≫ g)).hom.app L =
        (directImageCompIso f g).hom.app ((directImage r).obj L) ≫
          (directImageCompIso (g ≫ f) r).hom.app L ≫
            eqToHom (congrArg (fun s : T ⟶ X => (directImage s).obj L)
              (Category.assoc r g f).symm) := by
    simpa only [eqToIso.hom, Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id] using ht
  simpa only [directImageTriangleIso, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app, eqToHom_refl, Category.comp_id, Category.assoc] using hc.symm

lemma directImageTriangleIso_comp_transport {X Y Z T : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (t : Z ⟶ X) (ht : t = g ≫ f)
    (p : T ⟶ X) (q : T ⟶ Y) (r : T ⟶ Z)
    (hp : q ≫ f = p) (hq : r ≫ g = q) (hr : r ≫ t = p)
    (L : AbelianSheaf.{u, u + 1} T) :
    (directImageCompIso f g).hom.app ((directImage r).obj L) ≫
        eqToHom (congrArg (fun s : Z ⟶ X => (directImage s).obj ((directImage r).obj L))
          ht.symm) ≫ (directImageTriangleIso t p r hr).hom.app L =
      (directImage f).map ((directImageTriangleIso g q r hq).hom.app L) ≫
        (directImageTriangleIso f p q hp).hom.app L := by
  subst t
  simpa only [eqToHom_refl, Category.id_comp] using
    directImageTriangleIso_comp f g p q r hp hq L

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X)

/-- Normalize the reindexed comparison as a whole natural transformation first. -/
lemma diagramDirectImageComp_inv {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    ((diagramAdjunctionData X).compIso a b).inv =
      (directImageCompIso (X.map a).unop (X.map b).unop).hom ≫
        eqToHom (congrArg (fun s : X.obj i ⟶ X.obj k => directImage s.unop)
          (X.map_comp a b).symm) := rfl

/-- The actual reindexed right-comparison and the original cone triangles associate. -/
lemma diagramDirectImageTriangle_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k)
    (L : AbelianSheaf.{u, u + 1} c.pt.unop) :
    ((diagramAdjunctionData X).compIso a b).inv.app
        ((directImage (c.ι.app k).unop).obj L) ≫
      (diagramDirectImageTriangle X c (a ≫ b)).hom.app L =
    (directImage (X.map a).unop).map ((diagramDirectImageTriangle X c b).hom.app L) ≫
      (diagramDirectImageTriangle X c a).hom.app L := by
  have h := directImageTriangleIso_comp_transport (X.map a).unop (X.map b).unop
    (X.map (a ≫ b)).unop
    (congrArg (fun s : X.obj i ⟶ X.obj k => s.unop) (X.map_comp a b))
    (c.ι.app i).unop (c.ι.app j).unop (c.ι.app k).unop
    (coneSquare X c a) (coneSquare X c b) (coneSquare X c (a ≫ b)) L
  have hm := congrArg
    (fun α : directImage (X.map b).unop ⋙ directImage (X.map a).unop ⟶
        directImage (X.map (a ≫ b)).unop => α.app ((directImage (c.ι.app k).unop).obj L))
    (diagramDirectImageComp_inv X a b)
  simp only [NatTrans.comp_app, eqToHom_app] at hm
  have ht := congrArg
    (fun m : (directImage (X.map a).unop).obj
        ((directImage (X.map b).unop).obj ((directImage (c.ι.app k).unop).obj L)) ⟶
        (directImage (X.map (a ≫ b)).unop).obj ((directImage (c.ι.app k).unop).obj L) =>
      m ≫ (diagramDirectImageTriangle X c (a ≫ b)).hom.app L) hm
  exact ht.trans ((Category.assoc _ _ _).trans h)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
