/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.CoconeDoubleOpposite
public import Mathlib.CategoryTheory.Opposites

/-! # Original contravariant cocones of actual cone triangles

The native opposite and evaluation operations are retained. The comparison is
constructed from the actual cone triangle; evaluation uses its one computed
cone rather than an additional cone and equality proof as implementation data.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Limits.ConeTriangle

/-- Apply an actual contravariant functor to the original cone triangle. -/
def presheafCoconeIsoOfConeTriangle
    {J K C A : Type*} [Category* J] [Category* K] [Category* C] [Category* A]
    (D : J ⥤ C) (c : Cone D) (R : K ⥤ J) (T : K ⥤ C) (t : Cone T)
    (d : T ≅ R ⋙ D) (e : t.pt ≅ c.pt)
    (hw : ∀ k, t.π.app k ≫ d.hom.app k = e.hom ≫ c.π.app (R.obj k))
    (P : Cᵒᵖ ⥤ A) :
    (Cocone.precompose (Functor.isoWhiskerRight (NatIso.op d) P).hom).obj
      (P.mapCocone t.op) ≅ (P.mapCocone c.op).whisker R.op := by
  refine Cocone.ext (P.mapIso e.op).symm ?_
  intro k
  have h : e.inv ≫ t.π.app k.unop ≫ d.hom.app k.unop = c.π.app (R.obj k.unop) :=
    (congrArg (fun a => e.inv ≫ a) (hw k.unop)).trans (e.inv_hom_id_assoc _)
  change (P.map (d.hom.app k.unop).op ≫ P.map (t.π.app k.unop).op) ≫
      P.map e.inv.op = P.map (c.π.app (R.obj k.unop)).op
  simpa only [op_comp, Functor.map_comp, Category.assoc] using
    congrArg (fun a => P.map a.op) h

/-- Evaluate the actual opposite functor-cone operation at its computed cone. -/
def isColimitFunctorConeOpEvaluationEquiv
    {J C B A : Type*} [Category* J] [Category* C] [Category* B] [Category* A]
    (H : J ⥤ C ⥤ B) (c : Cone H) (P : Bᵒᵖ ⥤ A) (U : C) :
    IsColimit (((evaluation Cᵒᵖ A).obj (op U)).mapCocone
      ((Functor.opHom C B ⋙ (Functor.whiskeringRight Cᵒᵖ Bᵒᵖ A).obj P).mapCocone c.op)) ≃
      IsColimit (P.mapCocone (((evaluation C B).obj U).mapCone c).op) :=
  Equiv.refl _

end CategoryTheory.Limits.ConeTriangle
