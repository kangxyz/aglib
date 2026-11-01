/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.MvPowerSeries.Ideal
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # The original extended maximal ideal in a power-series spectrum

The point is literally the extended coefficient maximal ideal. Its primality
comes from the original coefficientwise residue map, whose kernel is that
ideal. No arbitrary prime is selected. Membership in an ambient open is not
asserted and must be supplied by the geometric argument.
-/

@[expose] public noncomputable section

open CategoryTheory MvPowerSeries IsLocalRing

namespace AlgebraicGeometry.Scheme

universe u
variable (σ : Type) (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- The literal extended maximal ideal is the kernel of coefficient reduction. -/
theorem powerSeries_residue_kernel :
    RingHom.ker (MvPowerSeries.map (residue A) (σ := σ)) =
      (maximalIdeal A).map (C : A →+* MvPowerSeries σ A) := by
  rw [MvPowerSeries.ker_map_of_fg (residue A)
    (RingHom.ker (residue A)).fg_of_isNoetherianRing, ker_residue]

/-- The original extended maximal ideal is prime, also for nondomain A. -/
theorem powerSeries_extendedMaximal_isPrime :
    ((maximalIdeal A).map (C : A →+* MvPowerSeries σ A)).IsPrime := by
  rw [← powerSeries_residue_kernel σ A]
  let : IsDomain (MvPowerSeries σ (ResidueField A)) := NoZeroDivisors.to_isDomain _
  exact RingHom.ker_isPrime _

/-- The original mB point, with no choice of an auxiliary closed-fibre point. -/
def powerSeriesClosedFiberPoint : Spec (.of (MvPowerSeries σ A)) :=
  ⟨(maximalIdeal A).map (C : A →+* MvPowerSeries σ A),
    powerSeries_extendedMaximal_isPrime σ A⟩

/-- The point retains precisely the original extended maximal ideal. -/
theorem powerSeriesClosedFiberPoint_asIdeal :
    (powerSeriesClosedFiberPoint σ A).asIdeal =
      (maximalIdeal A).map (C : A →+* MvPowerSeries σ A) := rfl

/-- Its contraction along the original constant map is the coefficient
maximal ideal, not merely an ideal contained in it. -/
theorem powerSeries_extendedMaximal_comap :
    ((maximalIdeal A).map (C : A →+* MvPowerSeries σ A)).comap C =
      maximalIdeal A := by
  rw [← powerSeries_residue_kernel σ A]
  ext a
  change MvPowerSeries.map (residue A) (C a : MvPowerSeries σ A) = 0 ↔ _
  rw [MvPowerSeries.map_C,
    ← map_zero (C : ResidueField A →+* MvPowerSeries σ (ResidueField A)),
    MvPowerSeries.C_inj, residue_eq_zero_iff]

/-- The same original mB point maps to the original closed coefficient point. -/
theorem powerSeriesClosedFiberPoint_image :
    Spec.map (CommRingCat.ofHom (C : A →+* MvPowerSeries σ A))
      (powerSeriesClosedFiberPoint σ A) = closedPoint A := by
  apply PrimeSpectrum.ext
  exact powerSeries_extendedMaximal_comap σ A

end AlgebraicGeometry.Scheme
