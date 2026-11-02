/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenBaseChangeIdentity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperOpenHorizontalCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionModel
public import Aglib.CategoryTheory.Adjunction.UnitMateHorizontal

/-! # Horizontal coherence of the original refinement unit maps

Original source-identity normalization turns the accepted horizontal mixed-mate
law into the horizontal unit equation. No torsion or invertibility is needed
for this map-level equality.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wAC wAD wBC wBD

variable (Λ : Type (u + 1)) [Ring Λ]
  {X AC AD BC BD : Scheme.{u}}
  (kC : X ⟶ AC) (kD : X ⟶ AD) (mC : AC ⟶ BC) (mD : AD ⟶ BD)
  [IsOpenImmersion kC] [IsOpenImmersion kD]
  [IsOpenImmersion mC] [IsOpenImmersion mD]
  (hA : AC ⟶ AD) (hB : BC ⟶ BD)
  (sqK : IsPullback kC (𝟙 X) hA kD) (sqM : IsPullback mC hA hB mD)
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wAC} (ModuleSheaf AC Λ)]
  [HasDerivedCategory.{wAD} (ModuleSheaf AD Λ)]
  [HasDerivedCategory.{wBC} (ModuleSheaf BC Λ)]
  [HasDerivedCategory.{wBD} (ModuleSheaf BD Λ)]

/-- The original refinement units respect horizontal composition of the opens. -/
theorem moduleUnboundedDerivedProperRefinementComparison_hComp :
    UnitMateHorizontalEquation
      (moduleUnboundedDerivedProperRefinementComparison kC kD hA sqK Λ)
      (moduleUnboundedDerivedProperRefinementComparison (kC ≫ mC) (kD ≫ mD) hB
        (sqK.paste_horiz sqM) Λ)
      (moduleUnboundedProperOpenMate hA mC mD hB sqM.flip Λ)
      (moduleUnboundedDerivedLowerShriekCompIso Λ mD kD)
      (moduleUnboundedDerivedLowerShriekCompIso Λ mC kC) := by
  apply unitMateHorizontalEquation (moduleUnboundedDerivedDirectImageIdIso Λ X)
    _ _
    (moduleUnboundedProperOpenMate (𝟙 X) kC kD hA sqK.flip Λ)
    (moduleUnboundedProperOpenMate (𝟙 X) (kC ≫ mC) (kD ≫ mD) hB
      (sqK.paste_horiz sqM).flip Λ) _ _ _
  · intro K
    exact (moduleUnboundedDerivedProperRefinementComparison_identitySourceMate kC kD hA sqK Λ
      K).symm
  · intro K
    exact (moduleUnboundedDerivedProperRefinementComparison_identitySourceMate
      (kC ≫ mC) (kD ≫ mD) hB (sqK.paste_horiz sqM) Λ K).symm
  · exact moduleUnboundedProperOpenMate_hComp Λ mD kD mC kC hB hA (𝟙 X)
      sqM.flip sqK.flip (sqK.paste_horiz sqM).flip

/-- The same original equation with specified actual total open maps, retaining
both original lower-shriek equality transports. -/
theorem moduleUnboundedDerivedProperRefinementComparison_hComp_transport
    (jC : X ⟶ BC) (jD : X ⟶ BD) [IsOpenImmersion jC] [IsOpenImmersion jD]
    (eC : kC ≫ mC = jC) (eD : kD ≫ mD = jD)
    (sqJ : IsPullback jC (𝟙 X) hB jD) :
    UnitMateHorizontalEquation
      (moduleUnboundedDerivedProperRefinementComparison kC kD hA sqK Λ)
      (moduleUnboundedDerivedProperRefinementComparison jC jD hB sqJ Λ)
      (moduleUnboundedProperOpenMate hA mC mD hB sqM.flip Λ)
      (eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ eD.symm) ≪≫
        moduleUnboundedDerivedLowerShriekCompIso Λ mD kD)
      (eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ eC.symm) ≪≫
        moduleUnboundedDerivedLowerShriekCompIso Λ mC kC) := by
  subst jC
  subst jD
  simpa only [eqToIso_refl, Iso.refl_trans] using
    moduleUnboundedDerivedProperRefinementComparison_hComp Λ kC kD mC mD hA hB sqK sqM

end AlgebraicGeometry.Scheme.EtaleCohomology
