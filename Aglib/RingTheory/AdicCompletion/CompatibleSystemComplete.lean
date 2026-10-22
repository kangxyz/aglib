/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.CompatibleSystemEffectivity

/-!
# Completeness of reconstructed compatible systems

Completeness is proved for the native module of compatible families using its
original projections and their exact kernels.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

namespace AdicCompletion.IsCompatibleSystem

universe u v

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {F : ℕᵒᵖ ⥤ ModuleCat.{v} R} (hF : IsCompatibleSystem I F)

include hF in
/-- The reconstructed native module is complete for the original ideal. -/
theorem sections_isAdicComplete (hI : I.FG) :
    IsAdicComplete I (ModuleCat.sectionsSubmodule F) := by
  let u := fun n => ModuleCat.sectionsEval F n
  have hu : ∀ {m n : ℕ} (h : m ≤ n),
      (towerTransition F h).comp (u n) = u m := by
    intro m n h
    ext x
    exact ModuleCat.map_sectionsEval F h x
  have hp : ∀ n, (I ^ n • ⊤ : Submodule R (ModuleCat.sectionsSubmodule F)) ≤
      (u n).ker := fun n => (hF.sectionsEval_ker_eq hI n).ge
  let q := completionToSections I F u hu hp
  have hq : Function.Injective q :=
    completionToSections_injective I F u hu hp 0
      (fun n => by simpa only [Nat.add_zero] using (hF.sectionsEval_ker_eq hI n).le)
  have hqof (x : ModuleCat.sectionsSubmodule F) : q (of I _ x) = x := by
    apply Subtype.ext
    funext j
    rfl
  apply (of_bijective_iff (I := I) (M := ModuleCat.sectionsSubmodule F)).mp
  constructor
  · intro x y h
    simpa only [hqof] using congrArg q h
  · intro x
    exact ⟨q x, hq (hqof (q x))⟩

end AdicCompletion.IsCompatibleSystem
