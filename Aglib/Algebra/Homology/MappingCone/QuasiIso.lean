/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
/-!
# Quasi-isomorphisms from acyclic mapping cones

The actual acyclicity of a cochain mapping cone implies that its defining map
is a quasi-isomorphism. This is a theorem in an arbitrary abelian category;
no derived-equivalence or geometric exactness assumption is used.
-/
@[expose] public section


noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated CochainComplex
namespace CochainComplex

/-- The converse cone criterion for genuine quasi-isomorphisms. -/
theorem quasiIso_of_mappingCone_acyclic {A : Type*} [Category* A] [Abelian A]
    {K L : CochainComplex A ℤ} (s : K ⟶ L) (h : (mappingCone s).Acyclic) : QuasiIso s := by
  let P := HomotopyCategory.subcategoryAcyclic A
  have hp : P ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (mappingCone s)) :=
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 h
  have hs := (P.trW_iff_of_distinguished (mappingCone.triangleh s)
      (HomotopyCategory.mappingCone_triangleh_distinguished s)).2 hp
  rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at hs
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff s).1 hs

end CochainComplex
