/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Filtered.InvertibleDiagram

/-! # Maps to a fixed target descend through the original canonical comparisons -/
@[expose] public noncomputable section
namespace CategoryTheory.Functor
open Opposite
variable {J E : Type*} [Category* J] [Category* E]
  (F : Jᵒᵖ ⥤ E) [∀ (i j : Jᵒᵖ) (f : i ⟶ j), IsIso (F.map f)]
  [IsCofilteredOrEmpty J] {T : E}

/-- A compatible map to a fixed target commutes with each original comparison. -/
theorem cofilteredComparison_toTarget
    (b : ∀ j : J, F.obj (op j) ⟶ T)
    (h : ∀ {i j : J} (a : i ⟶ j), F.map a.op ≫ b i = b j) (j k : J) :
    (F.cofilteredComparison j k).hom ≫ b k = b j := by
  let a := IsCofiltered.minToLeft j k
  let c := IsCofiltered.minToRight j k
  rw [F.cofilteredComparison_eq_span a c]
  change (F.map a.op ≫ (asIso (F.map c.op)).inv) ≫ b k = b j
  rw [← h c, Category.assoc, ← Category.assoc (asIso (F.map c.op)).inv]
  change F.map a.op ≫ ((asIso (F.map c.op)).inv ≫ (asIso (F.map c.op)).hom) ≫ b _ = b j
  rw [Iso.inv_hom_id, Category.id_comp]
  exact h a
end CategoryTheory.Functor
