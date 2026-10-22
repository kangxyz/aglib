/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineBoundedSheaf
public import Aglib.RingTheory.AdicCompletion.HomNaturality

/-! # The original bounded reconstruction comparison on formal sections

The constructed geometric completion morphism induces the already constructed
bounded pullback completion equivalence. The equation retains the actual tilde
unit and every original quotient unit; no faithful-completion hypothesis is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  {K : (Spec B).IdealSheafData} {F : AdicSystem (Spec B) K}
  {H : (Spec B).CoherentSheaf} (α : F ⟶ (completionFunctor (Spec B) K).obj H)

/-- The original formal section module retains its completed coefficient-ring action. -/
local instance : Module (AdicCompletion (affineIdeal B K) B) F.affineFormalSections :=
  F.affineFormalSectionsModule

omit [IsNoetherianRing B] in
/-- The actual tilde unit cancels the actual counit in a section presentation. -/
theorem tildeUnit_sectionsMap_counit (P : ModuleCat B) (M : (Spec B).Modules)
    (q : P ⟶ moduleSpecΓFunctor.obj M) :
    (tilde.toTildeΓNatIso.app P).hom ≫
      moduleSpecΓFunctor.map (tilde.map q ≫ M.fromTildeΓ) = q := by
  have hn : (tilde.toTildeΓNatIso.app P).hom ≫
      moduleSpecΓFunctor.map (tilde.map q) =
      q ≫ (tilde.toTildeΓNatIso.app (moduleSpecΓFunctor.obj M)).hom :=
    ((tilde.toTildeΓNatIso (R := B)).hom.naturality q).symm
  have ht : (tilde.toTildeΓNatIso.app (moduleSpecΓFunctor.obj M)).hom ≫
      moduleSpecΓFunctor.map M.fromTildeΓ = 𝟙 _ :=
    (tilde.adjunction (R := B)).right_triangle_components M
  rw [Functor.map_comp, ← Category.assoc, hn, Category.assoc, ht]
  exact Category.comp_id q

/-- The geometric reconstruction completion map, expressed on the completion
of its literal finite pullback module. -/
def affineReconstructionCompletionSectionsMap (t : ℕ)
    (h : AdicSystem.DefectsKilled K t α) :
    AdicCompletion (affineIdeal B K) (affineReconstructionModule α) →ₗ[
      AdicCompletion (affineIdeal B K) B] F.affineFormalSections := by
  let G := affineReconstructionSheaf α t h
  let := ((completionFunctor (Spec B) K).obj G).affineFormalSectionsModule
  exact (AdicSystem.affineFormalSectionsMap (affineReconstructionCompletionMap α t h)).comp
    ((affineCompletionSectionsEquiv B K G).toLinearMap.comp
      (AdicCompletion.congr (affineIdeal B K)
        (tilde.toTildeΓNatIso.app
          (ModuleCat.of B (affineReconstructionModule α))).toLinearEquiv).toLinearMap)

/-- On original elements the geometric map is the original first projection. -/
theorem affineReconstructionCompletionSectionsMap_of (t : ℕ)
    (h : AdicSystem.DefectsKilled K t α) (x : affineReconstructionModule α) :
    affineReconstructionCompletionSectionsMap α t h
      (AdicCompletion.of (affineIdeal B K) _ x) = x.val.1 := by
  apply Subtype.ext
  funext n
  let G := affineReconstructionSheaf α t h
  let P := ModuleCat.of B (affineReconstructionModule α)
  have hu : (idealSheafQuotientUnit (Spec B) (K ^ n.unop)).app G.obj ≫
      (affineReconstructionCompletionMap α t h).hom.app n =
        (affineReconstructionSheafStages α t h).app n :=
    idealSheafQuotientUnit_desc (Spec B) (K ^ n.unop)
      ((affineReconstructionSheafStages α t h).app n) (F.property.annihilated n.unop)
  have hs : (tilde.toTildeΓNatIso.app P).hom ≫
      moduleSpecΓFunctor.map ((idealSheafQuotientUnit (Spec B) (K ^ n.unop)).app G.obj) ≫
      moduleSpecΓFunctor.map ((affineReconstructionCompletionMap α t h).hom.app n) =
        affineReconstructionStageHom α n := by
    rw [← Functor.map_comp, hu]
    exact tildeUnit_sectionsMap_counit P (F.obj.obj n)
      (affineReconstructionStageHom α n)
  exact ConcreteCategory.congr_hom hs x

/-- Equality with the bounded algebraic equivalence follows from the original
unit equation, by completed-linear uniqueness for a finite source module. -/
theorem affineReconstructionCompletionSectionsMap_eq (t : ℕ)
    (h : AdicSystem.DefectsKilled K t α) :
    affineReconstructionCompletionSectionsMap α t h =
      (affineReconstructionModuleCompletionEquiv α t h).toLinearMap := by
  let : Module.Finite B (affineReconstructionModule α) :=
    affineReconstructionModule_finite α t h
  apply AdicCompletion.linearMap_ext_of_finite (affineIdeal B K)
  intro x
  rw [affineReconstructionCompletionSectionsMap_of,
    LinearEquiv.coe_coe, affineReconstructionModuleCompletionEquiv_of]

end AlgebraicGeometry.Scheme.Modules.Coherent
