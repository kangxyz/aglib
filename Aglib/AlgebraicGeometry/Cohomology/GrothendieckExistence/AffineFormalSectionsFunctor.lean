/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineEffectivityHom

/-! # Functoriality of the original completed affine sections

This packages the existing completed scalar action and the original compatible
family maps. It introduces no alternative formal-system category.
-/

@[expose] public noncomputable section
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem

universe u
variable (B : CommRingCat.{u}) [IsNoetherianRing B] (K : (Spec B).IdealSheafData)

/-- The actual completed-section module, with its canonical scalar action. -/
def affineFormalSectionsObject (F : AdicSystem (Spec B) K) :
    ModuleCat (AdicCompletion (affineIdeal B K) B) := by
  let := F.affineFormalSectionsModule
  exact ModuleCat.of _ F.affineFormalSections

/-- Original compatible families and original completed-linear maps form a functor. -/
def affineFormalSectionsFunctor :
    AdicSystem (Spec B) K ⥤ ModuleCat (AdicCompletion (affineIdeal B K) B) where
  obj F := affineFormalSectionsObject B K F
  map {F G} φ := by
    let := F.affineFormalSectionsModule
    let := G.affineFormalSectionsModule
    exact ModuleCat.ofHom (X := affineFormalSectionsObject B K F)
      (Y := affineFormalSectionsObject B K G) (affineFormalSectionsMap φ)
  map_id F := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  map_comp φ ψ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl

/-- An actual formal isomorphism induces an equivalence of the original
completed-section modules, with no separately chosen inverse. -/
def affineFormalSectionsIso {F G : AdicSystem (Spec B) K} (e : F ≅ G) :
    affineFormalSectionsObject B K F ≃ₗ[AdicCompletion (affineIdeal B K) B]
      affineFormalSectionsObject B K G :=
  ((affineFormalSectionsFunctor B K).mapIso e).toLinearEquiv

end AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
