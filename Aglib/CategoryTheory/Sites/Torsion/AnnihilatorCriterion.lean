/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.Sheaf
public import Mathlib.CategoryTheory.Sites.Abelian

/-! # An original identity annihilator implies internal torsion -/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Sheaf

universe u v w

/-- A positive annihilator of the actual identity annihilates every section,
so gives the existing internal local-torsion property. -/
theorem isTorsion_of_nsmul_id_eq_zero
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0) :
    IsTorsion F := by
  apply Presheaf.isLocallyTorsion_of_sectionwise
  intro U x
  refine ⟨n, hn, ?_⟩
  let E := sheafToPresheaf J AddCommGrpCat.{w} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U)
  have h : n • 𝟙 (E.obj F) = 0 := by
    simpa only [Functor.map_nsmul, Functor.map_id, Functor.map_zero] using
      congrArg E.map hF
  simpa using congrArg (fun a : E.obj F ⟶ E.obj F => a.hom x) h

end CategoryTheory.Sheaf
