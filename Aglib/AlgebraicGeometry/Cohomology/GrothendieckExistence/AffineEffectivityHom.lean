/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineEffectivity
public import Aglib.RingTheory.AdicCompletion.CompatibleSystemHom

/-! # Original morphisms on completed affine formal sections -/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  {K : (Spec B).IdealSheafData} {F G : AdicSystem (Spec B) K}

/-- Apply global sections to the original natural transformation. -/
abbrev affineSectionsMap (φ : F ⟶ G) : F.affineSectionsTower ⟶ G.affineSectionsTower :=
  Functor.whiskerRight φ.hom moduleSpecΓFunctor

/-- The original map of compatible families is completed-linear. -/
def affineFormalSectionsMap (φ : F ⟶ G) :
    let := F.affineFormalSectionsModule
    let := G.affineFormalSectionsModule
    F.affineFormalSections →ₗ[AdicCompletion (affineIdeal B K) B] G.affineFormalSections :=
  F.affineSections_isCompatibleSystem.sectionsMapCompletion
    G.affineSections_isCompatibleSystem
    (fun j => ((affineSectionsMap φ).app j).hom)
    (fun g x => ConcreteCategory.congr_hom ((affineSectionsMap φ).naturality g) x)

/-- Its projections are the original coefficient morphisms, not chosen replacements. -/
@[simp]
theorem affineFormalSectionsMap_apply (φ : F ⟶ G) (x : F.affineFormalSections)
    (j : ℕᵒᵖ) :
    (affineFormalSectionsMap φ x).val j = (affineSectionsMap φ).app j (x.val j) := rfl

/-- All original projections uniquely characterize the completed-linear map. -/
theorem affineFormalSectionsMap_unique (φ : F ⟶ G)
    (g : let := F.affineFormalSectionsModule
      let := G.affineFormalSectionsModule
      F.affineFormalSections →ₗ[AdicCompletion (affineIdeal B K) B] G.affineFormalSections)
    (hg : ∀ x j, (g x).val j = (affineSectionsMap φ).app j (x.val j)) :
    g = affineFormalSectionsMap φ := by
  let := F.affineFormalSectionsModule
  let := G.affineFormalSectionsModule
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext j
  exact hg x j

end AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
