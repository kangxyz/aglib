/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramAdjointCocone
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.SquareCoefficientAdjoint
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.ConeConstancy

/-! # Native composition coherence of the cone direct-image triangles -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge

/-- Specialize the original whole right-comparison law before evaluating a coefficient. -/
private lemma directImageTriangleIso_comp_transport_whole {X Y Z T : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (t : Z ⟶ X) (ht : t = g ≫ f)
    (p : T ⟶ X) (q : T ⟶ Y) (r : T ⟶ Z)
    (hp : q ≫ f = p) (hq : r ≫ g = q) (hr : r ≫ t = p) :
    (Functor.associator (directImage r) (directImage g) (directImage f)).hom ≫
        Functor.whiskerLeft (directImage r)
          ((directImageCompIso f g).hom ≫ eqToHom (congrArg directImage ht.symm)) ≫
          (directImageTriangleIso t p r hr).hom =
      Functor.whiskerRight (directImageTriangleIso g q r hq).hom (directImage f) ≫
        (directImageTriangleIso f p q hp).hom := by
  have h := schemeAdjunctionData.triangleRightIso_comp_transport_whole
    schemeAdjunctionData_coherent f.op g.op t.op p.op q.op r.op
    (congrArg Quiver.Hom.op ht) (congrArg Quiver.Hom.op hp)
    (congrArg Quiver.Hom.op hq) (congrArg Quiver.Hom.op hr)
  simp only [schemeTriangleRightIso_eq_directImageTriangleIso,
    schemeRightCompIso_eq_directImageCompIso, schemeRight_eq_directImage,
    Iso.symm_inv, Quiver.Hom.unop_op] at h ⊢
  exact h.symm

lemma directImageTriangleIso_comp {X Y Z T : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (p : T ⟶ X) (q : T ⟶ Y) (r : T ⟶ Z)
    (hp : q ≫ f = p) (hq : r ≫ g = q) (L : AbelianSheaf.{u, u + 1} T) :
    (directImageCompIso f g).hom.app ((directImage r).obj L) ≫
        (directImageTriangleIso (g ≫ f) p r
          (by rw [← Category.assoc, hq, hp])).hom.app L =
      (directImage f).map ((directImageTriangleIso g q r hq).hom.app L) ≫
        (directImageTriangleIso f p q hp).hom.app L := by
  have h := NatTrans.congr_app
    (directImageTriangleIso_comp_transport_whole f g (g ≫ f) rfl p q r hp hq
      (by rw [← Category.assoc, hq, hp])) L
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, eqToHom_refl, Category.id_comp,
    Category.comp_id] at h ⊢
  exact h

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
  have h := NatTrans.congr_app
    (directImageTriangleIso_comp_transport_whole f g t ht p q r hp hq hr) L
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, eqToHom_app, Category.id_comp, Category.assoc] at h ⊢
  exact h

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
  have h := (diagramConeAdjunctionData X c).right_comp_whole a b
  change Functor.whiskerRight (diagramDirectImageTriangle X c b).hom
        (directImage (X.map a).unop) ≫ (diagramDirectImageTriangle X c a).hom =
      (Functor.associator (directImage (c.ι.app k).unop)
        (directImage (X.map b).unop) (directImage (X.map a).unop)).hom ≫
        Functor.whiskerLeft (directImage (c.ι.app k).unop)
          ((diagramAdjunctionData X).compIso a b).inv ≫
          (diagramDirectImageTriangle X c (a ≫ b)).hom at h
  have hv := NatTrans.congr_app h L
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.id_comp] at hv
  exact hv.symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
