/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.CompatibleSystemComplete

/-! # The extended ideal on reconstructed compatible systems -/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

namespace AdicCompletion.IsCompatibleSystem

universe u v

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {F : ℕᵒᵖ ⥤ ModuleCat.{v} R} (hF : IsCompatibleSystem I F)

/-- The reconstructed action restricts to the original scalar action. -/
abbrev sectionsScalarTower :
    let := hF.sectionsCompletionModule
    IsScalarTower R (AdicCompletion I R) (ModuleCat.sectionsSubmodule F) := by
  let := hF.sectionsCompletionModule
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  apply Subtype.ext
  funext j
  exact hF.stageCompletionModule_of_smul j.unop r (x.val j)

/-- The original projection, now linear over the completed coefficient ring. -/
def sectionsEvalCompletion (n : ℕ) :
    let := hF.sectionsCompletionModule
    let := hF.stageCompletionModule n
    ModuleCat.sectionsSubmodule F →ₗ[AdicCompletion I R] F.obj (op n) := by
  let := hF.sectionsCompletionModule
  let := hF.stageCompletionModule n
  exact { (ModuleCat.sectionsEval F n).toAddHom with map_smul' := fun _ _ => rfl }

/-- Extended-ideal powers induce precisely the original ideal filtration. -/
theorem extendedPow_restrictScalars (n : ℕ) :
    let := hF.sectionsCompletionModule
    let := hF.sectionsScalarTower
    ((I.map (algebraMap R (AdicCompletion I R))) ^ n •
      (⊤ : Submodule (AdicCompletion I R) (ModuleCat.sectionsSubmodule F))).restrictScalars R =
      I ^ n • (⊤ : Submodule R (ModuleCat.sectionsSubmodule F)) := by
  let := hF.sectionsCompletionModule
  let := hF.sectionsScalarTower
  change ((I.map (algebraMap R (AdicCompletion I R))) ^ n •
    (⊤ : Submodule (AdicCompletion I R) (ModuleCat.sectionsSubmodule F))).restrictScalars R =
      I ^ n • (⊤ : Submodule R (ModuleCat.sectionsSubmodule F))
  rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq]
  rfl

/-- The completed-linear projection has exactly the extended ideal-power kernel. -/
theorem sectionsEvalCompletion_ker_eq (hI : I.FG) (n : ℕ) :
    let := hF.sectionsCompletionModule
    let := hF.stageCompletionModule n
    (hF.sectionsEvalCompletion n).ker =
      (I.map (algebraMap R (AdicCompletion I R))) ^ n •
        (⊤ : Submodule (AdicCompletion I R) (ModuleCat.sectionsSubmodule F)) := by
  let := hF.sectionsCompletionModule
  let := hF.stageCompletionModule n
  let := hF.sectionsScalarTower
  ext x
  have hm : x ∈ (I.map (algebraMap R (AdicCompletion I R))) ^ n •
        (⊤ : Submodule (AdicCompletion I R) (ModuleCat.sectionsSubmodule F)) ↔
      x ∈ I ^ n • (⊤ : Submodule R (ModuleCat.sectionsSubmodule F)) := by
    change x ∈ (((I.map (algebraMap R (AdicCompletion I R))) ^ n •
      (⊤ : Submodule (AdicCompletion I R) (ModuleCat.sectionsSubmodule F))).restrictScalars R) ↔ _
    rw [hF.extendedPow_restrictScalars n]
  change ModuleCat.sectionsEval F n x = 0 ↔ _
  rw [← LinearMap.mem_ker, hF.sectionsEval_ker_eq hI n]
  exact hm.symm

/-- Reduction over the completed ring recovers the original stage canonically. -/
def sectionsReductionEquivCompleted (hI : I.FG) (n : ℕ) :
    let := hF.sectionsCompletionModule
    let := hF.stageCompletionModule n
    (ModuleCat.sectionsSubmodule F ⧸
      ((I.map (algebraMap R (AdicCompletion I R))) ^ n •
        (⊤ : Submodule (AdicCompletion I R) (ModuleCat.sectionsSubmodule F)))) ≃ₗ[
          AdicCompletion I R] F.obj (op n) := by
  let := hF.sectionsCompletionModule
  let := hF.stageCompletionModule n
  exact (Submodule.quotEquivOfEq _ _ (hF.sectionsEvalCompletion_ker_eq hI n).symm).trans
    ((hF.sectionsEvalCompletion n).quotKerEquivOfSurjective (hF.sectionsEval_surjective n))

@[simp]
theorem sectionsReductionEquivCompleted_mk (hI : I.FG) (n : ℕ)
    (x : ModuleCat.sectionsSubmodule F) :
    let := hF.sectionsCompletionModule
    let := hF.stageCompletionModule n
    hF.sectionsReductionEquivCompleted hI n (Submodule.Quotient.mk x) =
      ModuleCat.sectionsEval F n x := by
  rfl

/-- Completeness is also completeness for the extended ideal in the completed ring. -/
theorem sections_isAdicComplete_extended (hI : I.FG) :
    let := hF.sectionsCompletionModule
    IsAdicComplete (I.map (algebraMap R (AdicCompletion I R)))
      (ModuleCat.sectionsSubmodule F) := by
  let := hF.sectionsCompletionModule
  let := hF.sectionsScalarTower
  exact (IsAdicComplete.map_algebraMap_iff (S := AdicCompletion I R) I
    (ModuleCat.sectionsSubmodule F)).mpr
    (hF.sections_isAdicComplete hI)

end AdicCompletion.IsCompatibleSystem
