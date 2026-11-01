/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.StructuralComparisons

/-! # The original direct-image transport around the refinement rectangle -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wBC wBD wTC wTD

variable (Λ : Type (u + 1)) [Ring Λ]

/-- The specified original direct-image transport around the commuting proper sides. -/
def moduleUnboundedProperOpenRefinementTargetIso
    {BC BD TC TD : Scheme.{u}} (rC : BC ⟶ TC) (rD : BD ⟶ TD)
    (hB : BC ⟶ BD) (hT : TC ⟶ TD) (hr : hB ≫ rD = rC ≫ hT)
    [HasDerivedCategory.{wBC} (ModuleSheaf BC Λ)]
    [HasDerivedCategory.{wBD} (ModuleSheaf BD Λ)]
    [HasDerivedCategory.{wTC} (ModuleSheaf TC Λ)]
    [HasDerivedCategory.{wTD} (ModuleSheaf TD Λ)] :
    moduleUnboundedDerivedDirectImage Λ rC ⋙ moduleUnboundedDerivedDirectImage Λ hT ≅
      moduleUnboundedDerivedDirectImage Λ hB ⋙ moduleUnboundedDerivedDirectImage Λ rD :=
  (moduleUnboundedDerivedDirectImageCompIso Λ hT rC).symm ≪≫
    eqToIso (congrArg (fun f : BC ⟶ TD => moduleUnboundedDerivedDirectImage Λ f) hr.symm) ≪≫
    moduleUnboundedDerivedDirectImageCompIso Λ rD hB

end AlgebraicGeometry.Scheme.EtaleCohomology
