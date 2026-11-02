/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Filtered.InvertibleDiagramToTarget
public import Aglib.CategoryTheory.NatTrans.TargetComparisonEquation

/-! # Canonical cofiltered descent at the shared whole-equation boundary -/
@[expose] public noncomputable section
namespace CategoryTheory.Functor
open Opposite
variable {J E : Type*} [Category* J] [Category* E]
  (F : Jᵒᵖ ⥤ E) [∀ (i j : Jᵒᵖ) (f : i ⟶ j), IsIso (F.map f)]
  [IsCofilteredOrEmpty J] {T : E}

/-- Preserve the shared target-equation head through canonical descent. -/
theorem cofilteredComparison_targetEquation
    (b : ∀ j : J, F.obj (op j) ⟶ T)
    (h : ∀ {i j : J} (a : i ⟶ j), TargetComparisonEquation (F.map a.op) (b i) (b j))
    (j k : J) : TargetComparisonEquation (F.cofilteredComparison j k).hom (b k) (b j) :=
  F.cofilteredComparison_toTarget b h j k
end CategoryTheory.Functor
