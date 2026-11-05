/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.SchemeLimitSections

/-! # Simultaneous retention of all marks in represented-section descent

One actual map from the limit descends as a whole. Consequently every mark
is retained simultaneously, without selecting a point or assuming the marked
source finitely presented. This applies in particular to all finite-fibre marks.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u

/-- The actual colimit factorization preserves all original marked maps. -/
theorem exists_represented_factorization_all_marks
    {I : Type u} [Category.{u} I] {X : Scheme.{u}}
    (D : I ⥤ Over X) (c : Cone D) (U : Over X)
    (hc : IsColimit (representedSectionsCocone D c U)) (a : c.pt ⟶ U) :
    ∃ (i : I) (b : D.obj i ⟶ U), c.π.app i ≫ b = a ∧
      ∀ (P : Scheme.{u}) (y : P ⟶ c.pt.left),
        (y ≫ (c.π.app i).left) ≫ b.left = y ≫ a.left := by
  obtain ⟨i, b, hb⟩ := Types.jointly_surjective_of_isColimit hc a
  have h : c.π.app i.unop ≫ b = a := hb
  refine ⟨i.unop, b, h, ?_⟩
  intro P y
  exact (Category.assoc y (c.π.app i.unop).left b.left).trans
    (congrArg (fun k => y ≫ k.left) h)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
