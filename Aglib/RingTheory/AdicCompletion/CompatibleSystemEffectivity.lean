/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.CompatibleSystemKernel
public import Aglib.RingTheory.AdicCompletion.CompatibleSystemScalars
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Finite effectivity of compatible module systems

The native inverse limit is finite over the completed ring, not over the
original ring. Its reductions are canonically the original terms and retain
the original projection maps. No global scheme algebraization is asserted.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped TensorProduct

namespace AdicCompletion

universe u v w

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {P : Type w} [AddCommGroup P] [Module R P]
variable (F : ℕᵒᵖ ⥤ ModuleCat.{v} R) (hF : IsCompatibleSystem I F)
variable (uMap : ∀ n : ℕ, P →ₗ[R] F.obj (op n))
variable (hu : ∀ {m n : ℕ} (h : m ≤ n),
  (towerTransition F h).comp (uMap n) = uMap m)
variable (hpow : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R P) ≤ (uMap n).ker)

/-- The original completed presentation map is linear over the completed ring. -/
def completionPresentation :
    let := hF.sectionsCompletionModule
    AdicCompletion I P →ₗ[AdicCompletion I R] ModuleCat.sectionsSubmodule F := by
  let := hF.sectionsCompletionModule
  exact
    { (completionToSections I F uMap hu hpow).toAddHom with
      map_smul' := by
        intro a x
        apply Subtype.ext
        funext j
        let := hF.stageQuotientModule j.unop
        obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I j.unop a)
        change quotientToTower I F uMap hpow j.unop (a.val j.unop • x.val j.unop) =
          evalₐ I j.unop a • quotientToTower I F uMap hpow j.unop (x.val j.unop)
        rw [val_smul_eq_evalₐ_smul, ← hr]
        exact (quotientToTower I F uMap hpow j.unop).map_smul r (x.val j.unop) }

namespace IsCompatibleSystem

variable {I F} (hF : IsCompatibleSystem I F)

include hF in
/-- A compatible family from any module is killed at level `n` by `Iⁿ`. -/
theorem pow_le_ker_sectionsEval_comp
    (g : P →ₗ[R] ModuleCat.sectionsSubmodule F) (n : ℕ) :
    (I ^ n • ⊤ : Submodule R P) ≤ ((ModuleCat.sectionsEval F n).comp g).ker := by
  apply Submodule.smul_le.mpr
  intro a ha x _
  change ((ModuleCat.sectionsEval F n).comp g) (a • x) = 0
  rw [map_smul]
  exact hF.annihilated n ⟨a, ha⟩ _

/-- Projection after a compatible family retains the original transition law. -/
theorem transition_comp_sectionsEval_comp
    (g : P →ₗ[R] ModuleCat.sectionsSubmodule F) {n m : ℕ} (h : n ≤ m) :
    (towerTransition F h).comp ((ModuleCat.sectionsEval F m).comp g) =
      (ModuleCat.sectionsEval F n).comp g := by
  ext x
  exact ModuleCat.map_sectionsEval F h (g x)

/-- The actual inverse limit of a compatible finite system is finite over the
completed ring. This is not a finite-module claim over the original ring. -/
theorem sections_finite :
    let := hF.sectionsCompletionModule
    Module.Finite (AdicCompletion I R) (ModuleCat.sectionsSubmodule F) := by
  let := hF.sectionsCompletionModule
  obtain ⟨r, g, hg⟩ := hF.exists_finite_free_generators
  let uMap := fun n => (ModuleCat.sectionsEval F n).comp g
  have hu : ∀ {m n : ℕ} (h : m ≤ n),
      (towerTransition F h).comp (uMap n) = uMap m :=
    fun h => transition_comp_sectionsEval_comp g h
  have hp := hF.pow_le_ker_sectionsEval_comp g
  let q := completionPresentation I F hF uMap hu hp
  have hq : Function.Surjective q :=
    completionToSections_surjective_of_compatibleSystem I F hF uMap hu hp hg
  let : Module.Finite (AdicCompletion I R) (AdicCompletion I (Fin r → R)) :=
    Module.Finite.of_surjective (ofTensorProduct I (Fin r → R))
      (ofTensorProduct_surjective_of_finite I (Fin r → R))
  exact Module.Finite.of_surjective q hq

include hF in
/-- The original limit projection has exactly the defining ideal-power kernel. -/
theorem sectionsEval_ker_eq (hI : I.FG) (n : ℕ) :
    (ModuleCat.sectionsEval F n).ker =
      I ^ n • (⊤ : Submodule R (ModuleCat.sectionsSubmodule F)) := by
  obtain ⟨r, g, hg⟩ := hF.exists_finite_free_generators
  exact sectionsEval_ker_eq_of_presentation I F hF
    (fun n => (ModuleCat.sectionsEval F n).comp g)
    (transition_comp_sectionsEval_comp g) (hF.pow_le_ker_sectionsEval_comp g) hg hI n

/-- The reconstructed coefficient reduces canonically to the original stage. -/
def sectionsReductionEquiv (hI : I.FG) (n : ℕ) :
    (ModuleCat.sectionsSubmodule F ⧸
      (I ^ n • (⊤ : Submodule R (ModuleCat.sectionsSubmodule F)))) ≃ₗ[R] F.obj (op n) :=
  (Submodule.quotEquivOfEq _ _ (hF.sectionsEval_ker_eq hI n).symm).trans
    ((ModuleCat.sectionsEval F n).quotKerEquivOfSurjective (hF.sectionsEval_surjective n))

@[simp]
theorem sectionsReductionEquiv_mk (hI : I.FG) (n : ℕ)
    (x : ModuleCat.sectionsSubmodule F) :
    hF.sectionsReductionEquiv hI n (Submodule.Quotient.mk x) = ModuleCat.sectionsEval F n x := by
  simp [sectionsReductionEquiv]

/-- The canonical reductions intertwine the original system maps with reduction
of the reconstructed module. -/
theorem sectionsReductionEquiv_transition (hI : I.FG) {n m : ℕ} (h : n ≤ m)
    (x : ModuleCat.sectionsSubmodule F ⧸
      (I ^ m • (⊤ : Submodule R (ModuleCat.sectionsSubmodule F)))) :
    F.map (homOfLE h).op (hF.sectionsReductionEquiv hI m x) =
      hF.sectionsReductionEquiv hI n
        (Submodule.factorPow I (ModuleCat.sectionsSubmodule F) h x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change F.map (homOfLE h).op
      (hF.sectionsReductionEquiv hI m (Submodule.Quotient.mk x)) =
        hF.sectionsReductionEquiv hI n (Submodule.Quotient.mk x)
    simpa only [sectionsReductionEquiv_mk] using ModuleCat.map_sectionsEval F h x

end IsCompatibleSystem

end AdicCompletion
