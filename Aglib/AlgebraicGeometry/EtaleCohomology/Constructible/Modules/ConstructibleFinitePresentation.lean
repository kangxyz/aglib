/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ConstructibleStages
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteGeneration
public import Mathlib.CategoryTheory.Presentable.Limits

/-! # Actual finite presentations of constructible fixed-ring coefficients

Finite generation selects an epimorphic original finite-colimit stage. Its
kernel remains constructible over the Noetherian coefficient ring, and a
second epimorphic stage supplies the actual relations. The original target
is the resulting cokernel, hence finitely presentable in its native category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u

attribute [local instance] ModuleCat.Sheaf.hasSheafify Cardinal.fact_isRegular_aleph0

variable (R : Type (u + 1)) [Ring R] [IsNoetherianRing R]
    {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]

/-- An actual constructible module is a quotient of an original constructible
finitely presentable stage over the same coefficient ring. -/
theorem exists_epi_from_constructible_finitelyPresentable
    (F : ModuleSheaf R X) (hF : IsConstructible F) :
    ∃ (P : ModuleSheaf R X) (q : P ⟶ F),
      IsConstructible P ∧ IsFinitelyPresentable.{u + 1} P ∧ Epi q := by
  obtain ⟨I, hI, hfilt, D, c, rfl, ⟨hc⟩, hstage⟩ :=
    NativeFreePresentation.exists_filtered_presentation R X F
  let := hI
  let : IsFiltered I := hfilt
  obtain ⟨i, hi⟩ := exists_epi_of_isColimit_of_isConstructible R hc hF
  exact ⟨D.obj i, c.ι.app i,
    NativeFreePresentation.finiteColimitStage_isConstructible R _ (hstage i),
    (NativeFreePresentation.finiteColimitStages_filteredGenerator R X).le_isCardinalPresentable
      _ (hstage i), hi⟩

/-- Original constructible module coefficients on a quasi-compact separated
scheme are finitely presentable over their same Noetherian coefficient ring. -/
theorem isFinitelyPresentable_of_isConstructible
    (F : ModuleSheaf R X) (hF : IsConstructible F) : IsFinitelyPresentable.{u + 1} F := by
  obtain ⟨P, q, hP, hFP, hq⟩ := exists_epi_from_constructible_finitelyPresentable R F hF
  let : Epi q := hq
  obtain ⟨Q, r, _, hFQ, hr⟩ := exists_epi_from_constructible_finitelyPresentable R
    (kernel q) (isConstructible_kernel q hP hF)
  let : Epi r := hr
  let d : Q ⟶ P := r ≫ kernel.ι q
  have hd : d ≫ q = 0 := by simp [d, Category.assoc]
  have hc : IsColimit (CokernelCofork.ofπ q hd) :=
    isCokernelEpiComp (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel q)) r rfl
  have (j : WalkingParallelPair) :
      IsFinitelyPresentable.{u + 1} ((parallelPair d 0).obj j) := by
    cases j with
    | zero => exact hFQ
    | one => exact hFP
  exact isCardinalPresentable_of_isColimit' (CokernelCofork.ofπ q hd) hc
    Cardinal.aleph0.{u + 1} ((hasCardinalLT_aleph0_iff _).mpr inferInstance)

/-- Constructibility internally supplies the original native stage predicate
needed for fixed-ring finite-diagram descent. -/
theorem finiteColimitStage_of_isConstructible
    (F : ModuleSheaf R X) (hF : IsConstructible F) :
    NativeFreePresentation.finiteColimitStages R X F := by
  let := isFinitelyPresentable_of_isConstructible R F hF
  exact NativeFreePresentation.finiteColimitStages_of_isFinitelyPresentable R X F

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
