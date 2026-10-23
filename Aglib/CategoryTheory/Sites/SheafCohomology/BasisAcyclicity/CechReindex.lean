/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.Comparison

/-! # Čech reindexing across equivalent index types

The index universes can differ. The comparison is the original categorical
product reindexing and commutes with every cosimplicial operator.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.Cech

universe c h a b w t

variable {C : Type c} [Category.{h} C] [HasFiniteProducts C]
  {A : Type a} [Category.{b} A] [HasProducts.{w} A] [HasProducts.{t} A]
  {ι : Type w} {κ : Type t} (U : ι → C) (e : κ ≃ ι) (P : Cᵒᵖ ⥤ A)

/-- Reindexing the original Čech cosimplicial object by an equivalence. -/
def cechCosimplicialReindexIso :
    (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ (U ∘ e)).cech).obj P ≅
      (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj P := by
  refine NatIso.ofComponents (fun n =>
    Pi.reindex (Equiv.piCongrRight (fun _ : Fin (n.len + 1) => e))
      (fun a : Fin (n.len + 1) → ι => P.obj (op (∏ᶜ fun i => U (a i))))) ?_
  intro n m g
  apply Pi.hom_ext
  intro a
  obtain ⟨b, rfl⟩ := (Equiv.piCongrRight (fun _ : Fin (m.len + 1) => e)).surjective a
  simp only [FormalCoproduct.cosimplicialObjectFunctor, FormalCoproduct.evalOp,
    FormalCoproduct.cech, FormalCoproduct.mapPower, Function.comp_def]
  simp only [FormalCoproduct.power_I, OrderHom.toFun_eq_coe, FormalCoproduct.power_obj,
    Functor.comp_obj, Functor.whiskeringLeft_obj_obj, Functor.rightOp_obj, Functor.comp_map,
    Functor.rightOp_map, Quiver.Hom.unop_op, Category.assoc, limit.lift_π, Fan.mk_pt,
    Fan.mk_π_app, Equiv.piCongrRight_apply, Pi.map_apply]
  erw [Pi.reindex_hom_π, Pi.lift_comp_π]
  exact (Pi.reindex_hom_π_assoc
    (Equiv.piCongrRight (fun _ : Fin (n.len + 1) => e))
    (fun a : Fin (n.len + 1) → ι => P.obj (op (∏ᶜ fun i => U (a i))))
    (fun x => b (g.toOrderHom x)) _).symm

variable [Preadditive A]

/-- The original alternating Čech complex is invariant under equivalent,
possibly differently sized, indexing types. -/
def cechComplexReindexIso :
    (cechComplexFunctor (U ∘ e)).obj P ≅ (cechComplexFunctor U).obj P :=
  (AlgebraicTopology.alternatingCofaceMapComplex A).mapIso (cechCosimplicialReindexIso U e P)

end CategoryTheory.Cech
