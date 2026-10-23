/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# The actual etale-local zero locus of a section

This locus uses original small-etale chart restrictions, not a Zariski
sheaf support construction. It is open because the actual chart arrows
are etale and therefore open.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Set

namespace AlgebraicGeometry.Scheme.Etale

universe u v

variable {X : Scheme.{u}} (F : X.Etaleᵒᵖ ⥤ Ab.{v}) {U : X.Etale}

/-- Points having an actual etale neighborhood on which the original section is zero. -/
def sectionZeroLocus (a : F.obj (op U)) : Set U.left :=
  {x | ∃ (V : X.Etale) (f : V ⟶ U) (y : V.left), f.left y = x ∧ F.map f.op a = 0}

/-- The etale-local zero locus is open in the original test scheme. -/
theorem isOpen_sectionZeroLocus (a : F.obj (op U)) : IsOpen (sectionZeroLocus F a) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨V, f, y, hy, hz⟩
  apply Filter.mem_of_superset (f.left.isOpenMap.isOpen_range.mem_nhds ⟨y, hy⟩)
  rintro z ⟨w, hw⟩
  exact ⟨V, f, w, hw, hz⟩

/-- Actual etale restriction carries a local zero neighborhood to one on the target test. -/
theorem mem_sectionZeroLocus_of_restriction {V : X.Etale} (f : V ⟶ U)
    (a : F.obj (op U)) {y : V.left} (hy : y ∈ sectionZeroLocus F (F.map f.op a)) :
    f.left y ∈ sectionZeroLocus F a := by
  obtain ⟨W, g, z, hz, ha⟩ := hy
  refine ⟨W, g ≫ f, z, ?_, ?_⟩
  · exact congrArg f.left hz
  · simpa only [op_comp, CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply] using ha

end AlgebraicGeometry.Scheme.Etale
