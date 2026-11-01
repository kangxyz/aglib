/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PowerSeriesFiniteEtaleMaps
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.SectionLifting

/-! # Actual finite-etale sections on punctured power-series neighbourhoods -/

@[expose] public noncomputable section

open CategoryTheory MvPowerSeries

namespace AlgebraicGeometry.Scheme

universe u

/-- A prescribed section on the original zero-section intersection lifts to
the unchanged finite-etale cover on the entire power-series open. -/
theorem powerSeriesPuncturedFiniteEtale_exists_section
    {σ : Type} [Finite σ] {A : Type u} [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (V : (Spec (.of (MvPowerSeries σ A))).Opens)
    (hdim : 2 ≤ ringKrullDim A)
    (hV : splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V =
      puncturedSpecOpen A)
    (C : FiniteEtale V.toScheme)
    (a : (splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V).toScheme ⟶
      C.obj.left)
    (ha : a ≫ C.obj.hom = Spec.map (CommRingCat.ofHom
      (constantCoeff : MvPowerSeries σ A →+* A)) ∣_ V) :
    ∃ s : V.toScheme ⟶ C.obj.left, s ≫ C.obj.hom = 𝟙 V.toScheme ∧
      (Spec.map (CommRingCat.ofHom
        (constantCoeff : MvPowerSeries σ A →+* A)) ∣_ V) ≫ s = a := by
  let := (powerSeriesPuncturedFiniteEtaleZeroSectionFullyFaithful V hdim hV).full
  exact FiniteEtale.exists_section_of_baseChange_full _ C a ha

end AlgebraicGeometry.Scheme
