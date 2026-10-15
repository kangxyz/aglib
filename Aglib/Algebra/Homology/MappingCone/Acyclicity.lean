/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.MappingCone.QuasiIso

/-!
Source: `Quillen/Algebra/Homology/MappingConeAcyclicity.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 34]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Acyclicity of the original quasi-isomorphism cone

The original distinguished mapping-cone triangle proves the forward cone
criterion for quasi-isomorphisms, complementing the existing converse theorem.
-/

@[expose] public section
noncomputable section

section
open CategoryTheory CategoryTheory.Pretriangulated CochainComplex
namespace CochainComplex
/-- The actual mapping cone of an original quasi-isomorphism is acyclic. -/
theorem mappingCone_acyclic_of_quasiIso {A : Type*} [Category* A] [Abelian A]
    {K L : CochainComplex A ℤ} (s : K ⟶ L) [QuasiIso s] : (mappingCone s).Acyclic := by
  let P := HomotopyCategory.subcategoryAcyclic A
  have hs := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2
    (show QuasiIso s from inferInstance)
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at hs
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
    ((P.trW_iff_of_distinguished (mappingCone.triangleh s)
      (HomotopyCategory.mappingCone_triangleh_distinguished s)).1 hs)
end CochainComplex
end
