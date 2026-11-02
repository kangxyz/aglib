/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PowerSeriesClosedFiberPoint
public import Aglib.AlgebraicGeometry.Morphisms.Flat.GenericPoints
public import Mathlib.AlgebraicGeometry.Fiber

/-! # The original power-series closed-fibre generic point

The previously constructed extended maximal ideal specializes to every point
over the coefficient closed point. Transport through the native fibre
homeomorphism gives the generic point of the actual scheme-theoretic fibre.
No prime or residue-fibre model is independently chosen.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Set MvPowerSeries IsLocalRing

namespace AlgebraicGeometry.Scheme

universe u

variable (σ : Type) (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- The original extended maximal ideal specializes to every point of the
literal coefficient closed fibre. -/
theorem powerSeriesClosedFiberPoint_specializes
    (q : Spec (.of (MvPowerSeries σ A)))
    (hq : Spec.map (CommRingCat.ofHom (C : A →+* MvPowerSeries σ A)) q =
      closedPoint A) :
    powerSeriesClosedFiberPoint σ A ⤳ q := by
  apply (PrimeSpectrum.le_iff_specializes _ _).mp
  change (maximalIdeal A).map C ≤ q.asIdeal
  rw [Ideal.map_le_iff_le_comap]
  have hc : q.asIdeal.comap C = maximalIdeal A := congrArg PrimeSpectrum.asIdeal hq
  rw [hc]

/-- The native scheme-theoretic fibre point corresponding to exactly mB. -/
def powerSeriesClosedFiberGenericPoint :
    (Spec.map (CommRingCat.ofHom (C : A →+* MvPowerSeries σ A))).fiber
      (closedPoint A) :=
  ((Spec.map (CommRingCat.ofHom (C : A →+* MvPowerSeries σ A))).fiberHomeo
    (closedPoint A)).symm
      ⟨powerSeriesClosedFiberPoint σ A, powerSeriesClosedFiberPoint_image σ A⟩

/-- Its projection is precisely the already defined extended maximal ideal. -/
theorem powerSeriesClosedFiberGenericPoint_image :
    (Spec.map (CommRingCat.ofHom (C : A →+* MvPowerSeries σ A))).fiberι
      (closedPoint A) (powerSeriesClosedFiberGenericPoint σ A) =
        powerSeriesClosedFiberPoint σ A :=
  (Spec.map (CommRingCat.ofHom (C : A →+* MvPowerSeries σ A))).fiberι_fiberHomeo_symm
    (closedPoint A) _

/-- The same point is generic for the entire actual coefficient fibre. -/
theorem powerSeriesClosedFiberGenericPoint_isGenericPoint :
    IsGenericPoint (powerSeriesClosedFiberGenericPoint σ A) Set.univ := by
  apply isGenericPoint_iff_specializes.mpr
  intro y
  constructor
  · intro _
    trivial
  · intro _
    let f := Spec.map (CommRingCat.ofHom (C : A →+* MvPowerSeries σ A))
    apply (f.fiberHomeo (closedPoint A)).isInducing.specializes_iff.mp
    apply Topology.IsInducing.subtypeVal.specializes_iff.mp
    have he : (f.fiberHomeo (closedPoint A))
        (powerSeriesClosedFiberGenericPoint σ A) =
          ⟨powerSeriesClosedFiberPoint σ A, powerSeriesClosedFiberPoint_image σ A⟩ :=
      (f.fiberHomeo (closedPoint A)).apply_symm_apply _
    rw [he]
    exact powerSeriesClosedFiberPoint_specializes σ A _
      ((f.fiberHomeo (closedPoint A)) y).property


/-- In particular this is a component-generic point, with no new choice. -/
theorem powerSeriesClosedFiberGenericPoint_mem_genericPoints :
    powerSeriesClosedFiberGenericPoint σ A ∈ genericPoints
      ((Spec.map (CommRingCat.ofHom (C : A →+* MvPowerSeries σ A))).fiber
        (closedPoint A)) := by
  have h := powerSeriesClosedFiberGenericPoint_isGenericPoint σ A
  let : IrreducibleSpace
      ((Spec.map (CommRingCat.ofHom (C : A →+* MvPowerSeries σ A))).fiber
        (closedPoint A)) := (irreducibleSpace_def _).mpr h.isIrreducible
  rw [genericPoints, Set.mem_ofPred_eq, h.def, irreducibleComponents_eq_singleton]
  exact Set.mem_singleton _

/-- A flat map out of the actual fibre sends the original mB point to an
actual component-generic point of its target. -/
theorem powerSeriesClosedFiberGenericPoint_map_flat
    {X : Scheme.{u}}
    (g : (Spec.map (CommRingCat.ofHom (C : A →+* MvPowerSeries σ A))).fiber
      (closedPoint A) ⟶ X) [Flat g] :
    g (powerSeriesClosedFiberGenericPoint σ A) ∈ genericPoints X :=
  EtaleCohomology.Curves.genericPoint_map_flat g
    ⟨powerSeriesClosedFiberGenericPoint σ A,
      powerSeriesClosedFiberGenericPoint_mem_genericPoints σ A⟩

end AlgebraicGeometry.Scheme
