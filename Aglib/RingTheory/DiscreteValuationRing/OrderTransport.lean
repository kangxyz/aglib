/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.OrderTransport.FieldMap

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
  exact (Ring.ordFrac_map_eq_of_ringEquiv e (RingHom.id K)
    (by simpa using he.symm) (z : K)).symm

end IsDiscreteValuationRing.FiniteNorm

/- Migration source: R5Lab/Aglib/RingTheory/DiscreteValuationRing/OrderTransport.lean.
SHA-256 551516c7d9b5d2315c78178d6e1e51bab71b4e7a16ca0126eac5f8a6398b6209. -/
