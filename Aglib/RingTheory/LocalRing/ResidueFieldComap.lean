/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# The residue field map over a ring map

For a ring map `σ : A →+* B` and `t ∈ Spec B` over `s = σ⁻¹ t`:

* `Ideal.ResidueField.mapComap σ t : κ(s) →+* κ(t)`, the map `Ideal.ResidueField.map` over `σ`;
* `Ideal.ResidueField.algebraMap_comp_eq_mapComap_comp`: the square
  `A → B → κ(t)`, `A → κ(s) → κ(t)` commutes;
* `Ideal.ResidueField.flat_mapComap`: `κ(s) → κ(t)` is flat, as every field extension is.
-/

@[expose] public section

noncomputable section

namespace Ideal.ResidueField

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The residue field map `κ(σ⁻¹ t) ⟶ κ(t)` over `σ`. -/
abbrev mapComap (σ : A →+* B) (t : PrimeSpectrum B) :
    (PrimeSpectrum.comap σ t).asIdeal.ResidueField →+* t.asIdeal.ResidueField :=
  Ideal.ResidueField.map (PrimeSpectrum.comap σ t).asIdeal t.asIdeal σ rfl

/-- The residue field square commutes. -/
theorem algebraMap_comp_eq_mapComap_comp (σ : A →+* B) (t : PrimeSpectrum B) :
    (algebraMap B t.asIdeal.ResidueField).comp σ =
      (mapComap σ t).comp (algebraMap A (PrimeSpectrum.comap σ t).asIdeal.ResidueField) :=
  RingHom.ext fun a => (Ideal.ResidueField.map_algebraMap _ _ σ rfl a).symm

/-- A field extension is flat. -/
theorem flat_mapComap (σ : A →+* B) (t : PrimeSpectrum B) : (mapComap σ t).Flat := by
  let := (mapComap σ t).toAlgebra
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

end Ideal.ResidueField
