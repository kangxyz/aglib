/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-! Compatible isomorphic DVRs have the same actual fraction-field order. -/

@[expose] public noncomputable section
namespace IsDiscreteValuationRing.FiniteNorm
/-- Compatible isomorphic DVRs give the same order on their common actual fraction field. -/
theorem ordFrac_eq_of_ringEquiv
    {R S K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Field K]
    [Algebra R K] [IsFractionRing R K] [Algebra S K] [IsFractionRing S K]
    (e : R ≃+* S) (he : (algebraMap S K).comp e.toRingHom = algebraMap R K)
    (z : Kˣ) : Ring.ordFrac R (z : K) = Ring.ordFrac S (z : K) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (K := K) hπ z.ne_zero
  have he' (a : R) : algebraMap S K (e a) = algebraMap R K a :=
    congrArg (fun g : R →+* K => g a) he
  have hπ' : Irreducible (e π) := (MulEquiv.irreducible_iff e.toMulEquiv).mpr hπ
  have hu' : IsUnit (e (u : R)) := u.isUnit.map e.toRingHom
  rw [hu, Units.smul_def, Algebra.smul_def, map_mul, map_mul,
    map_zpow₀, map_zpow₀, Ring.ordFrac_of_isUnit u.isUnit,
    ← he' (u : R), Ring.ordFrac_of_isUnit (K := K) hu',
    Ring.ordFrac_irreducible hπ, ← he' π, Ring.ordFrac_irreducible hπ']

end IsDiscreteValuationRing.FiniteNorm

/- Migration source: R5Lab/Aglib/RingTheory/DiscreteValuationRing/OrderTransport.lean.
SHA-256 551516c7d9b5d2315c78178d6e1e51bab71b4e7a16ca0126eac5f8a6398b6209. -/
