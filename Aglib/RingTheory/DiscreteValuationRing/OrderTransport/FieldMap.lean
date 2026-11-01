/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-! # Fraction-field order under compatible isomorphic DVRs

A compatible map between the two actual fraction fields preserves the native
order when its restriction is the specified DVR isomorphism. Uniformizer
factorization constructs the proof without replacing either fraction field or
its algebra structure. Zero and the original positive-uniformizer convention
are retained; all four carrier universes are independent.
-/

@[expose] public noncomputable section

universe uR uS uK uL

namespace Ring

/-- The actual fraction-field map preserves native order through a compatible
DVR isomorphism, including the value at zero. -/
theorem ordFrac_map_eq_of_ringEquiv
    {R : Type uR} {S : Type uS} {K : Type uK} {L : Type uL}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    (e : R ≃+* S) (f : K →+* L)
    (he : f.comp (algebraMap R K) = (algebraMap S L).comp e.toRingHom)
    (z : K) : ordFrac S (f z) = ordFrac R z := by
  by_cases hz : z = 0
  · simp [hz]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (K := K) hπ hz
  have he' (a : R) : f (algebraMap R K a) = algebraMap S L (e a) :=
    congrArg (fun g : R →+* L => g a) he
  have hπ' : Irreducible (e π) := (MulEquiv.irreducible_iff e.toMulEquiv).mpr hπ
  have hu' : IsUnit (e (u : R)) := u.isUnit.map e.toRingHom
  rw [hu, Units.smul_def, Algebra.smul_def]
  simp only [map_mul, map_zpow₀]
  rw [he' (u : R), he' π, ordFrac_of_isUnit (K := L) hu',
    ordFrac_of_isUnit (K := K) u.isUnit,
    ordFrac_irreducible (K := L) hπ', ordFrac_irreducible (K := K) hπ]

end Ring
