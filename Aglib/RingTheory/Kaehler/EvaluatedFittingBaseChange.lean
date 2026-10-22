/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FittingIdeal.BaseChange
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Etale.Kaehler

/-! # Evaluated differential Fitting ideals in actual base-change squares

The differential comparison is the native Kähler tensor equivalence. Evaluation
uses the specified commuting ring square. Only the original differential module
must be finite; no domain or finite-type hypothesis is imposed on a localization.
-/

@[expose] public noncomputable section

namespace KaehlerDifferential

section Pushout

variable (R R' B B' : Type*) [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
  [Algebra R R'] [Algebra R B] [Algebra R B'] [Algebra R' B'] [Algebra B B']
  [IsScalarTower R R' B'] [IsScalarTower R B B']
  [Algebra.IsPushout R R' B B'] [Module.Finite B (KaehlerDifferential R B)]

/-- Differential Fitting ideals commute with an actual coefficient pushout. -/
theorem fittingIdeal_of_isPushout (k : ℕ) :
    Module.fittingIdeal B' (KaehlerDifferential R' B') k =
      (Module.fittingIdeal B (KaehlerDifferential R B) k).map (algebraMap B B') := by
  rw [← Module.fittingIdeal_congr (tensorKaehlerEquiv R R' B B') k,
    Module.fittingIdeal_baseChange]

/-- Evaluation after actual base change is the extension of the original
EVALUATED ideal along the actual target map. The final ideal equality is proved,
not assumed as transport data. -/
theorem map_fittingIdeal_of_isPushout
    {S S' : Type*} [CommRing S] [CommRing S']
    (χ : B →+* S) (χ' : B' →+* S') (σ : S →+* S')
    (hpoint : χ'.comp (algebraMap B B') = σ.comp χ) (k : ℕ) :
    (Module.fittingIdeal B' (KaehlerDifferential R' B') k).map χ' =
      ((Module.fittingIdeal B (KaehlerDifferential R B) k).map χ).map σ := by
  rw [fittingIdeal_of_isPushout R R' B B', Ideal.map_map, hpoint, Ideal.map_map]

end Pushout

section SourceLocalization

variable (R B B' : Type*) [CommRing R] [CommRing B] [CommRing B']
  [Algebra R B] [Algebra R B'] [Algebra B B'] [IsScalarTower R B B']
  [Module.Finite B (KaehlerDifferential R B)]

/-- Source localization at fixed coefficients extends the original Fitting
ideal; it does not assert that the localization is finite type over the base. -/
theorem fittingIdeal_of_isLocalization (Q : Submonoid B) [IsLocalization Q B'] (k : ℕ) :
    Module.fittingIdeal B' (KaehlerDifferential R B') k =
      (Module.fittingIdeal B (KaehlerDifferential R B) k).map (algebraMap B B') :=
  Module.fittingIdeal_of_isLocalizedModule Q (KaehlerDifferential.map R R B B') k

/-- The localized source point is compared through its actual restriction. -/
theorem map_fittingIdeal_of_isLocalization
    (Q : Submonoid B) [IsLocalization Q B']
    {S S' : Type*} [CommRing S] [CommRing S']
    (χ : B →+* S) (χ' : B' →+* S') (σ : S →+* S')
    (hpoint : χ'.comp (algebraMap B B') = σ.comp χ) (k : ℕ) :
    (Module.fittingIdeal B' (KaehlerDifferential R B') k).map χ' =
      ((Module.fittingIdeal B (KaehlerDifferential R B) k).map χ).map σ := by
  rw [fittingIdeal_of_isLocalization R B B' Q, Ideal.map_map, hpoint, Ideal.map_map]

end SourceLocalization

section LocalizationSquare

variable (R R' B B' : Type*) [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
  [Algebra R R'] [Algebra R B] [Algebra R B'] [Algebra R' B'] [Algebra B B']
  [IsScalarTower R R' B'] [IsScalarTower R B B']
  [Module.Finite B (KaehlerDifferential R B)]

/-- Simultaneously localizing coefficients and source is the actual pushout,
so the same Fitting index is retained. In the parameter application, `R` here
is the polynomial parameter ring, not the original coefficient DVR. -/
theorem map_fittingIdeal_of_isLocalizationSquare
    (Q : Submonoid R) [IsLocalization Q R']
    [IsLocalization (Algebra.algebraMapSubmonoid B Q) B']
    {S S' : Type*} [CommRing S] [CommRing S']
    (χ : B →+* S) (χ' : B' →+* S') (σ : S →+* S')
    (hpoint : χ'.comp (algebraMap B B') = σ.comp χ) (k : ℕ) :
    (Module.fittingIdeal B' (KaehlerDifferential R' B') k).map χ' =
      ((Module.fittingIdeal B (KaehlerDifferential R B) k).map χ).map σ := by
  let : Algebra.IsPushout R R' B B' :=
    (Algebra.isPushout_of_isLocalization Q R' B B').symm
  exact map_fittingIdeal_of_isPushout R R' B B' χ χ' σ hpoint k

end LocalizationSquare

end KaehlerDifferential
