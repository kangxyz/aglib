/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.MappedCoverSectionRepresentatives
/-! # Reindexing actual relative section images -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleAffineBasis
universe u
theorem relativeSourceEquality_isIso {S X : Scheme.{u}}
    {f g : S ⟶ X} (h : g = f) : IsIso (relativeSourceEquality h) := by
  cases h
  change IsIso (𝟙 (Over.mk f))
  infer_instance

private theorem map_three {C : Type*} [Category* C] (P : Cᵒᵖ ⥤ Ab.{u + 1})
    {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (s : P.obj (op Z)) :
    P.map f.op (P.map g.op (P.map h.op s)) = P.map (f ≫ g ≫ h).op s := by
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

theorem map_triangle_cancel {C : Type*} [Category* C]
    (P : Cᵒᵖ ⥤ Ab.{u + 1}) {B' B Z Y : C}
    (E : B' ⟶ B) [IsIso E] (Q : B ⟶ Z) (H : Z ⟶ Y) (G : B' ⟶ Y)
    (h : E ≫ Q ≫ H = G) (s : P.obj (op B)) (v : P.obj (op Y))
    (hv : P.map G.op v = P.map E.op s) : P.map Q.op (P.map H.op v) = s := by
  apply (ConcreteCategory.bijective_of_isIso (P.map E.op)).injective
  exact (map_three P E Q H v).trans
    ((congrArg (fun z : B' ⟶ Y ↦ P.map z.op v) h).trans hv)

theorem exists_reindexed_section {I : Type u} [Category.{u} I]
    {X : Scheme.{u}} (P : (Over X)ᵒᵖ ⥤ Ab.{u + 1})
    (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I) (r : D.obj i ⟶ X)
    (k : I) (q : k ⟶ i) (s : P.obj (op (Over.mk (Y := c.pt) (c.π.app i ≫ r))))
    (h : ∃ (l : Over k) (v : P.obj (op (Over.mk (D.map l.hom ≫ (D.map q ≫ r))))),
      P.map (Over.homMk (c.π.app l.left)
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun z ↦ z ≫ (D.map q ≫ r)) (c.w l.hom)))
        (U := Over.mk (Y := c.pt) (c.π.app k ≫ (D.map q ≫ r)))
        (V := Over.mk (D.map l.hom ≫ (D.map q ≫ r)))).op v =
      P.map (relativeSourceEquality (S := c.pt)
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun z ↦ z ≫ r) (c.w q)))).op s) :
    ∃ (j : I) (a : j ⟶ i) (v : P.obj (op (Over.mk (D.map a ≫ r)))),
      P.map (Over.homMk (c.π.app j)
        ((Category.assoc _ _ _).symm.trans (congrArg (fun z ↦ z ≫ r) (c.w a)))
        (U := Over.mk (Y := c.pt) (c.π.app i ≫ r))
        (V := Over.mk (D.map a ≫ r))).op v = s := by
  let r' := D.map q ≫ r
  have hf : c.π.app k ≫ r' = c.π.app i ≫ r :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun z ↦ z ≫ r) (c.w q))
  let E := relativeSourceEquality (S := c.pt) hf
  obtain ⟨l, v, himage⟩ := h
  have hr : D.map (l.hom ≫ q) ≫ r = D.map l.hom ≫ r' :=
    (congrArg (fun z ↦ z ≫ r) (D.map_comp l.hom q)).trans (Category.assoc _ _ _)
  let Estage := relativeSourceEquality hr
  let v' := P.map Estage.op v
  let Q : Over.mk (Y := c.pt) (c.π.app i ≫ r) ⟶ Over.mk (D.map (l.hom ≫ q) ≫ r) :=
    Over.homMk (c.π.app l.left)
      ((Category.assoc _ _ _).symm.trans (congrArg (fun z ↦ z ≫ r) (c.w (l.hom ≫ q))))
  let G : Over.mk (Y := c.pt) (c.π.app k ≫ r') ⟶ Over.mk (D.map l.hom ≫ r') :=
    Over.homMk (c.π.app l.left)
      ((Category.assoc _ _ _).symm.trans (congrArg (fun z ↦ z ≫ r') (c.w l.hom)))
  have hgeom : E ≫ Q ≫ Estage = G := by
    apply Over.OverMorphism.ext
    change (𝟙 c.pt) ≫ c.π.app l.left ≫ 𝟙 (D.obj l.left) = c.π.app l.left
    simp only [Category.id_comp, Category.comp_id]
  have : IsIso E := relativeSourceEquality_isIso hf
  refine ⟨l.left, l.hom ≫ q, v', ?_⟩
  exact map_triangle_cancel P E Q Estage G hgeom s v himage


end AlgebraicGeometry.Scheme.EtaleAffineBasis
