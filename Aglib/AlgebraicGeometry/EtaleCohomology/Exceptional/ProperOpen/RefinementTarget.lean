/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Composition

/-! # The original direct-image transport around the refinement rectangle -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wBC wBD wTC wTD

variable (Λ : Type (u + 1)) [Ring Λ]

/-- The specified original direct-image transport around the commuting proper sides. -/
def moduleProperOpenRefinementTargetIso
    {BC BD TC TD : Scheme.{u}} (rC : BC ⟶ TC) (rD : BD ⟶ TD)
    (hB : BC ⟶ BD) (hT : TC ⟶ TD) (hr : hB ≫ rD = rC ≫ hT)
    [HasDerivedCategory.{wBC} (ModuleSheaf BC Λ)]
    [HasDerivedCategory.{wBD} (ModuleSheaf BD Λ)]
    [HasDerivedCategory.{wTC} (ModuleSheaf TC Λ)]
    [HasDerivedCategory.{wTD} (ModuleSheaf TD Λ)] :
    moduleDerivedDirectImage Λ rC ⋙ moduleDerivedDirectImage Λ hT ≅
      moduleDerivedDirectImage Λ hB ⋙ moduleDerivedDirectImage Λ rD :=
  (moduleDerivedDirectImageCompIso Λ hT rC).symm ≪≫
    eqToIso (congrArg (fun f : BC ⟶ TD => moduleDerivedDirectImage Λ f) hr.symm) ≪≫
    moduleDerivedDirectImageCompIso Λ rD hB

end AlgebraicGeometry.Scheme.EtaleCohomology
