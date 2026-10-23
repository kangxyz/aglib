/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.Comparison
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Čech change of category without a thinness hypothesis

The comparison uses the original product comparison maps. Naturality is proved
on each product projection, so all simplex operators, not only cofaces, agree.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.Cech

universe u v u' v' a b w

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {D : Type u'} [Category.{v'} D] [HasFiniteProducts D]
  {A : Type a} [Category.{b} A] [HasProducts.{w} A]
  (F : C ⥤ D) [PreservesFiniteProducts F] {ι : Type w} (V : ι → C)
  (P : Dᵒᵖ ⥤ A)

/-- Actual product comparison for Čech objects in arbitrary, possibly non-thin categories. -/
def cechCosimplicialProductChangeIso :
    (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ V).cech).obj
      (F.op ⋙ P) ≅
    (FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.mk _ (fun i => F.obj (V i))).cech).obj P := by
  refine NatIso.ofComponents (fun n => Limits.Pi.mapIso fun a =>
    P.mapIso (PreservesProduct.iso F (fun i : Fin (n.len + 1) => V (a i))).op.symm) ?_
  intro n m g
  apply Limits.Pi.hom_ext
  intro a
  change Fin (m.len + 1) → ι at a
  dsimp [FormalCoproduct.cosimplicialObjectFunctor,
    FormalCoproduct.evalOp, FormalCoproduct.cech, FormalCoproduct.mapPower]
  simp only [Category.assoc, Pi.mapIso_hom_π, Iso.symm_hom, Functor.mapIso_inv, Iso.op_inv,
    limit.lift_π_assoc, Fan.mk_pt, Discrete.functor_obj_eq_as, Fan.mk_π_app, ← Functor.map_comp,
    limit.lift_π, Pi.mapIso_hom_π_assoc, Function.comp_apply]
  congr 2
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, Quiver.Hom.unop_op]
  apply (cancel_mono (PreservesProduct.iso F _).hom).mp
  apply Pi.hom_ext
  intro j
  simp only [Function.comp_apply, PreservesProduct.iso_hom, Category.assoc,
    map_lift_piComparison, limit.lift_π, Fan.mk_pt, Fan.mk_π_app]
  change (PreservesProduct.iso F (V ∘ a)).inv ≫
      F.map (Pi.π (V ∘ a) (g.toOrderHom j)) =
    (Pi.lift fun x => Pi.π (fun k => F.obj (V (a k))) (g.toOrderHom x)) ≫
      (PreservesProduct.iso F (V ∘ a ∘ g.toOrderHom)).inv ≫
      (PreservesProduct.iso F (V ∘ a ∘ g.toOrderHom)).hom ≫ Pi.π _ j
  rw [Iso.inv_hom_id_assoc]
  erw [Pi.lift_comp_π]
  rw [Iso.inv_comp_eq]
  exact (piComparison_comp_π F (V ∘ a) (g.toOrderHom j)).symm

variable [Preadditive A]

/-- Change of category for the original alternating Čech complexes. -/
def cechComplexProductChangeIso :
    (cechComplexFunctor V).obj (F.op ⋙ P) ≅
      (cechComplexFunctor (fun i => F.obj (V i))).obj P :=
  (AlgebraicTopology.alternatingCofaceMapComplex A).mapIso
    (cechCosimplicialProductChangeIso F V P)

end CategoryTheory.Cech
