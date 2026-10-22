/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.CompatibleSystemScalars
public import Aglib.Algebra.Category.ModuleCat.NatTowerExactUniverses

/-!
# Maps between reconstructed compatible systems

The map is the native map of compatible families, with its canonical completed
scalar linearity. The two systems may have independent carrier universes.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

namespace AdicCompletion.IsCompatibleSystem

universe u v w

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {F : ℕᵒᵖ ⥤ ModuleCat.{v} R} {G : ℕᵒᵖ ⥤ ModuleCat.{w} R}
variable (hF : IsCompatibleSystem I F) (hG : IsCompatibleSystem I G)
variable (φ : ∀ j, F.obj j →ₗ[R] G.obj j)
variable (hφ : ∀ {j k} (f : j ⟶ k) x, φ k (F.map f x) = G.map f (φ j x))

/-- The original compatible-family map is linear over the completed ring. -/
def sectionsMapCompletion :
    let := hF.sectionsCompletionModule
    let := hG.sectionsCompletionModule
    ModuleCat.sectionsSubmodule F →ₗ[AdicCompletion I R] ModuleCat.sectionsSubmodule G := by
  let := hF.sectionsCompletionModule
  let := hG.sectionsCompletionModule
  exact
    { (ModuleCat.sectionsMapOfLinearMaps φ hφ).toAddHom with
      map_smul' := by
        intro a x
        apply Subtype.ext
        funext j
        let := hF.stageQuotientModule j.unop
        let := hG.stageQuotientModule j.unop
        change φ j (evalₐ I j.unop a • x.val j) = evalₐ I j.unop a • φ j (x.val j)
        obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I j.unop a)
        rw [← hr]
        exact (φ j).map_smul r (x.val j) }

/-- Evaluation of the reconstructed map is the supplied original stage map. -/
@[simp]
theorem sectionsMapCompletion_apply (x : ModuleCat.sectionsSubmodule F) (j : ℕᵒᵖ) :
    (hF.sectionsMapCompletion hG φ hφ x).val j = φ j (x.val j) := rfl

/-- Maps into the native limit are determined by the original projections. -/
theorem sectionsMapCompletion_unique
    (f : let := hF.sectionsCompletionModule
      let := hG.sectionsCompletionModule
      ModuleCat.sectionsSubmodule F →ₗ[AdicCompletion I R] ModuleCat.sectionsSubmodule G)
    (hf : ∀ x j, (f x).val j = φ j (x.val j)) :
    f = hF.sectionsMapCompletion hG φ hφ := by
  let := hF.sectionsCompletionModule
  let := hG.sectionsCompletionModule
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext j
  exact hf x j

end AdicCompletion.IsCompatibleSystem
