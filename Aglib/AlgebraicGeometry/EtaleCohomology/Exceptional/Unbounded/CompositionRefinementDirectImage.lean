/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperOpenRefinementRectangle
public import Aglib.CategoryTheory.Functor.ImageStructuralRectangle

/-! # The original structural direct-image face of a composition refinement

The two proper factorizations use the actual direct-image compositors and
actual equality transports. Their structural face follows from the accepted
over-base composition law, not from an assumed cube.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wA wB wC wD wZ

variable (Λ : Type (u + 1)) [Ring Λ]

/-- Original over-base direct-image comparison at its literal composite. -/
theorem moduleUnboundedDerivedDirectImageOverIso_rfl {A B Z : Scheme.{u}}
    (a : A ⟶ B) (p : B ⟶ Z)
    [HasDerivedCategory.{wA} (ModuleSheaf A Λ)]
    [HasDerivedCategory.{wB} (ModuleSheaf B Λ)]
    [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)] :
    moduleUnboundedDerivedDirectImageOverIso Λ (a ≫ p) p a rfl =
      (moduleUnboundedDerivedDirectImageCompIso Λ p a).symm := by
  simp only [moduleUnboundedDerivedDirectImageOverIso, eqToIso_refl, Iso.trans_refl]

/-- Equality transport of the proper side preserves the original over-base map. -/
theorem moduleUnboundedDerivedDirectImageOverIso_transport {A B Z : Scheme.{u}}
    (pA : A ⟶ Z) (pB : B ⟶ Z) (a b : A ⟶ B) (e : a = b)
    (ha : a ≫ pB = pA) (hb : b ≫ pB = pA)
    [HasDerivedCategory.{wA} (ModuleSheaf A Λ)]
    [HasDerivedCategory.{wB} (ModuleSheaf B Λ)]
    [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)] :
    Functor.isoWhiskerRight
        (eqToIso (congrArg (fun k : A ⟶ B => moduleUnboundedDerivedDirectImage Λ k) e))
        (moduleUnboundedDerivedDirectImage Λ pB) ≪≫
      moduleUnboundedDerivedDirectImageOverIso Λ pA pB b hb =
        moduleUnboundedDerivedDirectImageOverIso Λ pA pB a ha := by
  subst b
  simp

/-- The exact structural-image face, with the same named original rectangle iso. -/
theorem moduleUnboundedDerivedDirectImageOverIso_rectangle
    {A B C D Z : Scheme.{u}} (rC : A ⟶ C) (rD : B ⟶ D)
    (hB : A ⟶ B) (hT : C ⟶ D) (pC : C ⟶ Z) (pD : D ⟶ Z)
    (hr : hB ≫ rD = rC ≫ hT) (hp : hT ≫ pD = pC)
    (hTotal : hB ≫ (rD ≫ pD) = rC ≫ pC)
    [HasDerivedCategory.{wA} (ModuleSheaf A Λ)]
    [HasDerivedCategory.{wB} (ModuleSheaf B Λ)]
    [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]
    [HasDerivedCategory.{wD} (ModuleSheaf D Λ)]
    [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)] :
    ImageCompositionStructuralEquation
      (moduleUnboundedDerivedDirectImageOverIso Λ pC pD hT hp)
      (moduleUnboundedProperOpenRefinementTargetIso Λ rC rD hB hT hr)
      (moduleUnboundedDerivedDirectImageCompIso Λ pD rD).symm
      (moduleUnboundedDerivedDirectImageCompIso Λ pC rC).symm
      (moduleUnboundedDerivedDirectImageOverIso Λ (rC ≫ pC) (rD ≫ pD) hB hTotal) := by
  have hC : (rC ≫ hT) ≫ pD = rC ≫ pC := by rw [Category.assoc, hp]
  have hD : (hB ≫ rD) ≫ pD = rC ≫ pC := (Category.assoc _ _ _).trans hTotal
  exact imageCompositionStructuralEquation_of_triangles
    (moduleUnboundedDerivedDirectImageOverIso Λ pC pD hT hp)
    (moduleUnboundedProperOpenRefinementTargetIso Λ rC rD hB hT hr)
    (moduleUnboundedDerivedDirectImageCompIso Λ pD rD).symm
    (moduleUnboundedDerivedDirectImageCompIso Λ pC rC).symm
    (moduleUnboundedDerivedDirectImageOverIso Λ (rC ≫ pC) (rD ≫ pD) hB hTotal)
    (moduleUnboundedDerivedDirectImageOverIso Λ (rD ≫ pD) pD rD rfl)
    (moduleUnboundedDerivedDirectImageOverIso Λ (rC ≫ pC) pC rC rfl)
    (moduleUnboundedDerivedDirectImageOverIso_rfl Λ rD pD)
    (moduleUnboundedDerivedDirectImageOverIso_rfl Λ rC pC)
    (moduleUnboundedDerivedDirectImageCompIso Λ hT rC)
    (moduleUnboundedDerivedDirectImageCompIso Λ rD hB)
    (eqToIso (congrArg (fun k : A ⟶ D => moduleUnboundedDerivedDirectImage Λ k) hr.symm))
    (moduleUnboundedDerivedDirectImageOverIso Λ (rC ≫ pC) pD (rC ≫ hT) hC)
    (moduleUnboundedDerivedDirectImageOverIso Λ (rC ≫ pC) pD (hB ≫ rD) hD)
    (moduleUnboundedDerivedDirectImageOverIso_comp Λ (rC ≫ pC) pC pD rC hT rfl hp hC)
    (moduleUnboundedDerivedDirectImageOverIso_comp Λ (rC ≫ pC) (rD ≫ pD) pD
      hB rD hTotal rfl hD)
    (moduleUnboundedDerivedDirectImageOverIso_transport Λ (rC ≫ pC) pD
      (rC ≫ hT) (hB ≫ rD) hr.symm hC hD) rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
