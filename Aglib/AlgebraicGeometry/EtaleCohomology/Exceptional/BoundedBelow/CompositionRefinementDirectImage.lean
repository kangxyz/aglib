/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.RefinementRectangle
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
theorem moduleDerivedDirectImageOverIso_rfl {A B Z : Scheme.{u}}
    (a : A ⟶ B) (p : B ⟶ Z)
    [HasDerivedCategory.{wA} (ModuleSheaf A Λ)]
    [HasDerivedCategory.{wB} (ModuleSheaf B Λ)]
    [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)] :
    moduleDerivedDirectImageOverIso Λ (a ≫ p) p a rfl =
      (moduleDerivedDirectImageCompIso Λ p a).symm := by
  simp only [moduleDerivedDirectImageOverIso, eqToIso_refl, Iso.trans_refl]

/-- Equality transport of the proper side preserves the original over-base map. -/
theorem moduleDerivedDirectImageOverIso_transport {A B Z : Scheme.{u}}
    (pA : A ⟶ Z) (pB : B ⟶ Z) (a b : A ⟶ B) (e : a = b)
    (ha : a ≫ pB = pA) (hb : b ≫ pB = pA)
    [HasDerivedCategory.{wA} (ModuleSheaf A Λ)]
    [HasDerivedCategory.{wB} (ModuleSheaf B Λ)]
    [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)] :
    Functor.isoWhiskerRight
        (eqToIso (congrArg (fun k : A ⟶ B => moduleDerivedDirectImage Λ k) e))
        (moduleDerivedDirectImage Λ pB) ≪≫
      moduleDerivedDirectImageOverIso Λ pA pB b hb =
        moduleDerivedDirectImageOverIso Λ pA pB a ha := by
  subst b
  simp

/-- The exact structural-image face, with the same named original rectangle iso. -/
theorem moduleDerivedDirectImageOverIso_rectangle
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
      (moduleDerivedDirectImageOverIso Λ pC pD hT hp)
      (moduleProperOpenRefinementTargetIso Λ rC rD hB hT hr)
      (moduleDerivedDirectImageCompIso Λ pD rD).symm
      (moduleDerivedDirectImageCompIso Λ pC rC).symm
      (moduleDerivedDirectImageOverIso Λ (rC ≫ pC) (rD ≫ pD) hB hTotal) := by
  have hC : (rC ≫ hT) ≫ pD = rC ≫ pC := by rw [Category.assoc, hp]
  have hD : (hB ≫ rD) ≫ pD = rC ≫ pC := (Category.assoc _ _ _).trans hTotal
  exact imageCompositionStructuralEquation_of_triangles
    (moduleDerivedDirectImageOverIso Λ pC pD hT hp)
    (moduleProperOpenRefinementTargetIso Λ rC rD hB hT hr)
    (moduleDerivedDirectImageCompIso Λ pD rD).symm
    (moduleDerivedDirectImageCompIso Λ pC rC).symm
    (moduleDerivedDirectImageOverIso Λ (rC ≫ pC) (rD ≫ pD) hB hTotal)
    (moduleDerivedDirectImageOverIso Λ (rD ≫ pD) pD rD rfl)
    (moduleDerivedDirectImageOverIso Λ (rC ≫ pC) pC rC rfl)
    (moduleDerivedDirectImageOverIso_rfl Λ rD pD)
    (moduleDerivedDirectImageOverIso_rfl Λ rC pC)
    (moduleDerivedDirectImageCompIso Λ hT rC)
    (moduleDerivedDirectImageCompIso Λ rD hB)
    (eqToIso (congrArg (fun k : A ⟶ D => moduleDerivedDirectImage Λ k) hr.symm))
    (moduleDerivedDirectImageOverIso Λ (rC ≫ pC) pD (rC ≫ hT) hC)
    (moduleDerivedDirectImageOverIso Λ (rC ≫ pC) pD (hB ≫ rD) hD)
    (moduleDerivedDirectImageOverIso_comp Λ (rC ≫ pC) pC pD rC hT rfl hp hC)
    (moduleDerivedDirectImageOverIso_comp Λ (rC ≫ pC) (rD ≫ pD) pD
      hB rD hTotal rfl hD)
    (moduleDerivedDirectImageOverIso_transport Λ (rC ≫ pC) pD
      (rC ≫ hT) (hB ≫ rD) hr.symm hC hD) rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
