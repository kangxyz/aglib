/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.Colimit
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-! # Torsion through additive sequential-colimit functors

An additive group-valued functor preserving sequential colimits sends an
internally torsion sheaf to a torsion group. The proof uses the original
factorial annihilator cocone, not a uniform annihilator of the input sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.Sheaf

universe u v w w'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}]

/-- Additivity and sequential-colimit preservation send internal local torsion
to ordinary elementwise torsion in the original group-valued functor. -/
theorem IsTorsion.isAddTorsion_obj
    {F : Sheaf J AddCommGrpCat.{w}} (hF : IsTorsion F)
    (H : Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w'}) [H.Additive]
    [PreservesColimitsOfShape ℕ H] : IsAddTorsion (H.obj F) := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{w'}) :=
    preservesFilteredColimitsOfSize_of_univLE.{w', w', 0, 0}
      (forget AddCommGrpCat.{w'})
  let hc := isColimitOfPreserves H (factorialAnnihilatorCoconeIsColimit F hF)
  intro x
  obtain ⟨n, y, hy⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget AddCommGrpCat.{w'}) hc) x
  change ↥(H.obj (annihilator F (n + 1).factorial)) at y
  change H.map (annihilatorι F (n + 1).factorial) y = x at hy
  have he : (n + 1).factorial •
      𝟙 (H.obj ((factorialAnnihilatorDiagram F).obj n)) = 0 := by
    simpa only [Functor.map_nsmul, Functor.map_id, Functor.map_zero] using
      congrArg H.map (factorialAnnihilatorDiagram_annihilated F n)
  have hyzero : (n + 1).factorial • y = 0 :=
    ConcreteCategory.congr_hom he y
  apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
  refine ⟨(n + 1).factorial, Nat.factorial_pos _, ?_⟩
  rw [← hy, ← map_nsmul, hyzero, map_zero]

end CategoryTheory.Sheaf
