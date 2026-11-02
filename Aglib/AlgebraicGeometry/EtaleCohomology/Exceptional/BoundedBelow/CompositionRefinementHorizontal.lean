/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRefinement
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.HorizontalCoherence
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
theorem moduleDerivedProperRefinementComparison_hComp :
    UnitMateHorizontalEquation
      (moduleDerivedProperRefinementComparison kC kD hA sqK Λ)
      (moduleDerivedProperRefinementComparison (kC ≫ mC) (kD ≫ mD) hB
        (sqK.paste_horiz sqM) Λ)
      (moduleProperOpenMate Λ mD mC hA hB sqM.flip)
      (moduleDerivedLowerShriekCompIso Λ mD kD)
      (moduleDerivedLowerShriekCompIso Λ mC kC) := by
  apply unitMateHorizontalEquation (moduleDerivedDirectImageIdIso Λ X)
    _ _
    (moduleProperOpenMate Λ kD kC (𝟙 X) hA sqK.flip)
    (moduleProperOpenMate Λ (kD ≫ mD) (kC ≫ mC) (𝟙 X) hB
      (sqK.paste_horiz sqM).flip) _ _ _
  · intro K
    exact (moduleDerivedProperRefinementComparison_identitySourceMate kC kD hA sqK Λ K).symm
  · intro K
    exact (moduleDerivedProperRefinementComparison_identitySourceMate
      (kC ≫ mC) (kD ≫ mD) hB (sqK.paste_horiz sqM) Λ K).symm
  · exact moduleProperOpenMate_hComp Λ mD kD mC kC hB hA (𝟙 X)
      sqM.flip sqK.flip (sqK.paste_horiz sqM).flip

/-- The same original equation with specified actual total open maps, retaining
both original lower-shriek equality transports. -/
theorem moduleDerivedProperRefinementComparison_hComp_transport
    (jC : X ⟶ BC) (jD : X ⟶ BD) [IsOpenImmersion jC] [IsOpenImmersion jD]
    (eC : kC ≫ mC = jC) (eD : kD ≫ mD = jD)
    (sqJ : IsPullback jC (𝟙 X) hB jD) :
    UnitMateHorizontalEquation
      (moduleDerivedProperRefinementComparison kC kD hA sqK Λ)
      (moduleDerivedProperRefinementComparison jC jD hB sqJ Λ)
      (moduleProperOpenMate Λ mD mC hA hB sqM.flip)
      (eqToIso (moduleDerivedLowerShriek_congr Λ eD.symm) ≪≫
        moduleDerivedLowerShriekCompIso Λ mD kD)
      (eqToIso (moduleDerivedLowerShriek_congr Λ eC.symm) ≪≫
        moduleDerivedLowerShriekCompIso Λ mC kC) := by
  subst jC
  subst jD
  simpa only [eqToIso_refl, Iso.refl_trans] using
    moduleDerivedProperRefinementComparison_hComp Λ kC kD mC mD hA hB sqK sqM

end AlgebraicGeometry.Scheme.EtaleCohomology
