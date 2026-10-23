/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.Comparison
public import Mathlib.Algebra.Category.Grp.Ulift

/-! # Value lifting of arbitrary small-cover Čech complexes

The comparison uses the native product comparison, including every alternating
coface. The cover need not be finite. This leaf concerns the original product
Čech complex, independently of any sheaf-acyclicity argument.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.BasisAcyclicity

universe c h v t

variable {C : Type c} [Category.{h} C] [HasFiniteProducts C]
  {ι : Type v} (U : ι → C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v})

/-- The original arbitrary-small-cover Čech complex commutes with value lift. -/
def cechValueLiftIso :
    (AddCommGrpCat.uliftFunctor.{t, v}.mapHomologicalComplex _).obj
        ((cechComplexFunctor U).obj P) ≅
      (cechComplexFunctor U).obj (P ⋙ AddCommGrpCat.uliftFunctor.{t, v}) :=
  Cech.cechComplexCoefficientIso AddCommGrpCat.uliftFunctor U P

/-- Exactness of the actual small-cover cochains survives coefficient ULift. -/
theorem cechValueLift_exactAt (n : ℕ) (hP : ((cechComplexFunctor U).obj P).ExactAt n) :
    ((cechComplexFunctor U).obj (P ⋙ AddCommGrpCat.uliftFunctor.{t, v})).ExactAt n := by
  apply HomologicalComplex.ExactAt.of_iso _ (cechValueLiftIso U P)
  rw [HomologicalComplex.exactAt_iff]
  exact ((HomologicalComplex.exactAt_iff _ _).mp hP).map AddCommGrpCat.uliftFunctor

end CategoryTheory.Sheaf.BasisAcyclicity
