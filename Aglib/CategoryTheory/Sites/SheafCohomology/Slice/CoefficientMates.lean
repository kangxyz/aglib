/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Coefficients
public import Aglib.CategoryTheory.Adjunction.LowerShriekUnderlying

/-!
# The original lower-shriek coefficient comparison is an adjunction mate

Coproduct preservation and coefficient-compatible sheafification give the actual comparison.
Its proved unit law identifies its mate with literal restriction before any site or coefficient
is specialized. The underlying counit follows from the whole mate equation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf.SliceCohomology

universe u v uA vA uB vB

variable {C : Type u} [Category.{v} C]
  {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  [HasCoproducts.{v} A] [HasCoproducts.{v} B]
  (F : A ⥤ B) [∀ (ι : Type v), PreservesColimitsOfShape (Discrete ι) F]
  (U : C) (J : GrothendieckTopology C)
  [HasWeakSheafify J A] [HasWeakSheafify J B]
  [J.HasSheafCompose F] [(J.over U).HasSheafCompose F] [J.PreservesSheafification F]

-- Preserve the original slice/sheaf-compose reduction at this mate boundary.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual coefficient comparison has the literal restriction comparison as its mate. -/
theorem mate_lowerShriekCoefficientIso :
    (mateEquiv (lowerShriekAdjunction J A U) (lowerShriekAdjunction J B U)
      (TwoSquare.mk _ _ _ _ (lowerShriekCoefficientIso F U J).hom)).natTrans = 𝟙 _ := by
  apply mateEquiv_inv_natTrans_eq_of_unit _ _ (lowerShriekCoefficientIso F U J).symm
  intro M
  have h := lowerShriekCoefficientIso_unit F U J M
  simp only [NatTrans.id_app, Iso.symm_hom]
  erw [Category.id_comp]
  rw [← h, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  exact (congrArg (fun k => (lowerShriekAdjunction J B U).unit.app
      ((sheafCompose (J.over U) F).obj M) ≫ k)
      ((J.overPullback B U).map_id _)).trans (Category.comp_id _)

end CategoryTheory.Sheaf.SliceCohomology
