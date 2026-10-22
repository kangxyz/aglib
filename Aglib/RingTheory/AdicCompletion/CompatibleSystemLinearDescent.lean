/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.CompatibleSystemExtended
public import Aglib.RingTheory.AdicCompletion.CompatibleSystemHom

/-! # Original stage maps from a linear map of compatible limits

A map initially linear only over the original ring descends through the
actual evaluation kernels. Its reconstructed completed-linear map has the
same underlying map. No compatibility property is imposed on an intermediate
tower used to construct that original linear map.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AdicCompletion.IsCompatibleSystem

universe u v w
variable {R : Type u} [CommRing R] {I : Ideal R}
  {F : ℕᵒᵖ ⥤ ModuleCat.{v} R} {G : ℕᵒᵖ ⥤ ModuleCat.{w} R}
  (hF : IsCompatibleSystem I F) (hG : IsCompatibleSystem I G) (hI : I.FG)
  (f : ModuleCat.sectionsSubmodule F →ₗ[R] ModuleCat.sectionsSubmodule G)

/-- Descent through the original ideal-power quotient and original evaluation. -/
def linearDescendStage (n : ℕ) : F.obj (op n) →ₗ[R] G.obj (op n) :=
  ((I ^ n • (⊤ : Submodule R (ModuleCat.sectionsSubmodule F))).liftQ
    ((ModuleCat.sectionsEval G n).comp f)
    (hG.pow_le_ker_sectionsEval_comp f n)).comp
      (hF.sectionsReductionEquiv hI n).symm.toLinearMap

/-- Every descended map retains the original projection equation. -/
theorem linearDescendStage_eval (n : ℕ) (x : ModuleCat.sectionsSubmodule F) :
    hF.linearDescendStage hG hI f n (ModuleCat.sectionsEval F n x) =
      ModuleCat.sectionsEval G n (f x) := by
  rw [← hF.sectionsReductionEquiv_mk hI n x]
  change ((I ^ n • (⊤ : Submodule R (ModuleCat.sectionsSubmodule F))).liftQ
    ((ModuleCat.sectionsEval G n).comp f) (hG.pow_le_ker_sectionsEval_comp f n))
    ((hF.sectionsReductionEquiv hI n).symm
      ((hF.sectionsReductionEquiv hI n) (Submodule.Quotient.mk x))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- Original projections uniquely determine the descended stage map. -/
theorem linearDescendStage_unique (n : ℕ)
    (g : F.obj (op n) →ₗ[R] G.obj (op n))
    (hg : ∀ x, g (ModuleCat.sectionsEval F n x) = ModuleCat.sectionsEval G n (f x)) :
    g = hF.linearDescendStage hG hI f n := by
  ext y
  obtain ⟨x, rfl⟩ := hF.sectionsEval_surjective n y
  exact (hg x).trans (hF.linearDescendStage_eval hG hI f n x).symm

/-- Descent respects every original transition, not only adjacent stages. -/
theorem linearDescendStage_naturality {j k : ℕᵒᵖ} (a : j ⟶ k) (x : F.obj j) :
    hF.linearDescendStage hG hI f k.unop (F.map a x) =
      G.map a (hF.linearDescendStage hG hI f j.unop x) := by
  obtain ⟨z, rfl⟩ := hF.sectionsEval_surjective j.unop x
  change hF.linearDescendStage hG hI f k.unop (F.map a (z.val j)) = _
  have hz : F.map a (z.val j) = z.val k := z.property a
  rw [hz]
  change hF.linearDescendStage hG hI f k.unop (ModuleCat.sectionsEval F k.unop z) =
    G.map a (hF.linearDescendStage hG hI f j.unop (ModuleCat.sectionsEval F j.unop z))
  rw [linearDescendStage_eval, linearDescendStage_eval]
  have hfz : G.map a ((f z).val j) = (f z).val k := (f z).property a
  exact hfz.symm

/-- The actual descended compatible family provides completed scalar linearity. -/
def linearDescendCompletion :
    let := hF.sectionsCompletionModule
    let := hG.sectionsCompletionModule
    ModuleCat.sectionsSubmodule F →ₗ[AdicCompletion I R] ModuleCat.sectionsSubmodule G :=
  hF.sectionsMapCompletion hG (fun j => hF.linearDescendStage hG hI f j.unop)
    (fun a x => hF.linearDescendStage_naturality hG hI f a x)

/-- The completed-linear reconstruction is the same original compatible-section map. -/
theorem linearDescendCompletion_apply (x : ModuleCat.sectionsSubmodule F) :
    hF.linearDescendCompletion hG hI f x = f x := by
  apply Subtype.ext
  funext j
  exact hF.linearDescendStage_eval hG hI f j.unop x

/-- No coercion of an arbitrary original-linear map to completed scalars is assumed. -/
theorem linearDescendCompletion_restrictScalars :
    let := hF.sectionsCompletionModule
    let := hG.sectionsCompletionModule
    let := hF.sectionsScalarTower
    let := hG.sectionsScalarTower
    (hF.linearDescendCompletion hG hI f).restrictScalars R = f := by
  let := hF.sectionsCompletionModule
  let := hG.sectionsCompletionModule
  let := hF.sectionsScalarTower
  let := hG.sectionsScalarTower
  apply LinearMap.ext
  intro x
  exact hF.linearDescendCompletion_apply hG hI f x

end AdicCompletion.IsCompatibleSystem
