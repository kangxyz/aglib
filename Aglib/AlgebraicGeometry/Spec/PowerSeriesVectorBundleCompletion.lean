/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PowerSeriesUnitSectionCone
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.VectorBundleFullness
public import Mathlib.RingTheory.MvPowerSeries.Equiv

/-! # Original vector-bundle completion on punctured power-series neighbourhoods

On the original open, normal Noetherian local Hartogs data constructs the
scalar cone. Native quasi-affineness and the actual generator/kernel lifting
then prove bijectivity of the original quotient-tower map on Hom sets.
This is the normal-base full-faithfulness statement, not effectivity or the
arbitrary depth-two nonnormal version.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPowerSeries

namespace AlgebraicGeometry.Scheme

open Modules Modules.Coherent
universe u

/-- Original vector-bundle maps are recovered uniquely from the original formal tower. -/
theorem powerSeriesPuncturedVectorBundleHom_bijective
    {σ : Type} [Finite σ] {A : Type u} [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (V : (Spec (.of (MvPowerSeries σ A))).Opens)
    (hdim : 2 ≤ ringKrullDim A)
    (hV : splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V =
      puncturedSpecOpen A)
    (M N : V.toScheme.Modules)
    [IsFiniteLocallyFree V M] [IsFiniteLocallyFree V N] :
    Function.Bijective (idealSheafQuotientTowerHom V
      (idealThickeningIdealSheaf V.ι (RingHom.ker
        (constantCoeff : MvPowerSeries σ A →+* A))) (F := M) (G := N)) := by
  let : CompactSpace V := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact
      (V : Set (Spec (.of (MvPowerSeries σ A)))))
  let : V.toScheme.IsQuasiAffine := IsQuasiAffine.of_isImmersion V.ι
  have hunitData := powerSeriesPuncturedUnitSectionCone_isLimit V hdim hV
  obtain ⟨hunit⟩ := hunitData
  exact idealSheafQuotientTowerHom_bijective_of_unit V _ M N hunit

end AlgebraicGeometry.Scheme
