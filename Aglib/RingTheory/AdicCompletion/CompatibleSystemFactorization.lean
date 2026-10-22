/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.CompatibleSystemLinearDescent

/-! # Factorization through a comparison invertible on compatible sections

The intermediate tower is arbitrary. Only the source and the genuine target
are adic compatible systems. In particular, the stage comparison need not be
injective: uniqueness uses the entire family and injectivity on its limit.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AdicCompletion.IsCompatibleSystem

universe u v w z
variable {R : Type u} [CommRing R] {I : Ideal R}
  {F : ℕᵒᵖ ⥤ ModuleCat.{v} R} {G : ℕᵒᵖ ⥤ ModuleCat.{w} R}
  {T : ℕᵒᵖ ⥤ ModuleCat.{z} R}
  (hF : IsCompatibleSystem I F) (hG : IsCompatibleSystem I G) (hI : I.FG)
  (ψ : ∀ j, G.obj j →ₗ[R] T.obj j)
  (hψ : ∀ {j k} (a : j ⟶ k) x, ψ k (G.map a x) = T.map a (ψ j x))
  (hψb : Function.Bijective (ModuleCat.sectionsMapOfLinearMaps ψ hψ))
  (γ : ∀ j, F.obj j →ₗ[R] T.obj j)
  (hγ : ∀ {j k} (a : j ⟶ k) x, γ k (F.map a x) = T.map a (γ j x))

/-- The original limit map followed by the inverse original comparison. -/
def factorizationLimit :
    ModuleCat.sectionsSubmodule F →ₗ[R] ModuleCat.sectionsSubmodule G :=
  (LinearEquiv.ofBijective (ModuleCat.sectionsMapOfLinearMaps ψ hψ) hψb).symm.toLinearMap.comp
    (ModuleCat.sectionsMapOfLinearMaps γ hγ)

/-- The original limit comparison equation. -/
theorem factorizationLimit_comparison (x : ModuleCat.sectionsSubmodule F) :
    ModuleCat.sectionsMapOfLinearMaps ψ hψ
      (factorizationLimit ψ hψ hψb γ hγ x) =
        ModuleCat.sectionsMapOfLinearMaps γ hγ x :=
  (LinearEquiv.ofBijective (ModuleCat.sectionsMapOfLinearMaps ψ hψ) hψb).apply_symm_apply _

/-- Descend to the actual stages, not to the possibly noncompatible intermediate tower. -/
def factorizationStage (n : ℕ) : F.obj (op n) →ₗ[R] G.obj (op n) :=
  hF.linearDescendStage hG hI (factorizationLimit ψ hψ hψb γ hγ) n

/-- Every descended stage satisfies the original comparison diagram. -/
theorem factorizationStage_comparison (n : ℕ) (x : F.obj (op n)) :
    ψ (op n) (hF.factorizationStage hG hI ψ hψ hψb γ hγ n x) = γ (op n) x := by
  obtain ⟨s, rfl⟩ := hF.sectionsEval_surjective n x
  change ψ (op n) (hF.linearDescendStage hG hI
    (factorizationLimit ψ hψ hψb γ hγ) n (ModuleCat.sectionsEval F n s)) = _
  rw [linearDescendStage_eval]
  exact congrArg (fun t : ModuleCat.sectionsSubmodule T => t.val (op n))
    (factorizationLimit_comparison ψ hψ hψb γ hγ s)

/-- The descended comparison preserves all original transition maps. -/
theorem factorizationStage_naturality {j k : ℕᵒᵖ} (a : j ⟶ k) (x : F.obj j) :
    hF.factorizationStage hG hI ψ hψ hψb γ hγ k.unop (F.map a x) =
      G.map a (hF.factorizationStage hG hI ψ hψ hψb γ hγ j.unop x) :=
  hF.linearDescendStage_naturality hG hI _ a x

/-- The WHOLE compatible family is unique. No finite-stage injectivity is used. -/
theorem factorizationStage_unique
    (α : ∀ j, F.obj j →ₗ[R] G.obj j)
    (hα : ∀ {j k} (a : j ⟶ k) x, α k (F.map a x) = G.map a (α j x))
    (hαψ : ∀ j x, ψ j (α j x) = γ j x) (n : ℕ) :
    α (op n) = hF.factorizationStage hG hI ψ hψ hψb γ hγ n := by
  apply hF.linearDescendStage_unique hG hI
  intro x
  have hx : ModuleCat.sectionsMapOfLinearMaps α hα x =
      factorizationLimit ψ hψ hψb γ hγ x := by
    apply hψb.injective
    rw [factorizationLimit_comparison]
    apply Subtype.ext
    funext j
    exact hαψ j (x.val j)
  exact congrArg (fun s : ModuleCat.sectionsSubmodule G => s.val (op n)) hx

/-- The same comparison is genuinely linear over the completed ring. -/
def factorizationCompletion :
    let := hF.sectionsCompletionModule
    let := hG.sectionsCompletionModule
    ModuleCat.sectionsSubmodule F →ₗ[AdicCompletion I R] ModuleCat.sectionsSubmodule G :=
  hF.linearDescendCompletion hG hI (factorizationLimit ψ hψ hψb γ hγ)

/-- Completed scalar linearity does not change the original limit map. -/
theorem factorizationCompletion_apply (x : ModuleCat.sectionsSubmodule F) :
    hF.factorizationCompletion hG hI ψ hψ hψb γ hγ x =
      factorizationLimit ψ hψ hψb γ hγ x :=
  hF.linearDescendCompletion_apply hG hI _ x

end AdicCompletion.IsCompatibleSystem
