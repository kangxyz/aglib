/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.Artinian.Ring

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/Length/ResidueDimension.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`c6169be8008b9bfd168810ae6d6948955f715552181df919390e7bd8c919bb09`.
-/

@[expose] public section

noncomputable section
open IsLocalRing
namespace Module
section LocalLength

variable (k R M : Type*) [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
variable [Module.Finite k (ResidueField R)]

/-- The length over the actual base field includes the full residue-field degree. -/
theorem length_over_field_eq_local_length_mul_residue_finrank :
    Module.length k M =
      Module.length R M * (Module.finrank k (ResidueField R) : ℕ∞) := by
  rw [IsLocalRing.length_restrictScalars k R M]
  rw [← Module.length_eq_of_surjective (M := ResidueField R)
    (residue_surjective (R := k)), Module.length_eq_finrank]

/-- Finite local length and finite residue degree imply finite base-field dimension. -/
theorem finite_over_field_of_finite_local_length (hM : IsFiniteLength R M) :
    Module.Finite k M := by
  have hR : Module.length R M ≠ ⊤ := Module.length_ne_top_iff.mpr hM
  have hlen : Module.length k M ≠ ⊤ := by
    rw [length_over_field_eq_local_length_mul_residue_finrank k R M,
      ← ENat.natCast_toNat hR, ← Nat.cast_mul]
    exact ENat.natCast_ne_top _
  have hfin := Module.length_ne_top_iff.mp hlen
  let : IsNoetherian k M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).1
  infer_instance

/-- Integer local multiplicity times residue degree is the actual vector-space dimension. -/
theorem finrank_eq_local_length_mul_residue_finrank (hM : IsFiniteLength R M) :
    Module.finrank k M =
      (Module.length R M).toNat * Module.finrank k (ResidueField R) := by
  let := finite_over_field_of_finite_local_length k R M hM
  have h := congrArg ENat.toNat
    (length_over_field_eq_local_length_mul_residue_finrank k R M)
  simpa [Module.length_eq_finrank, ENat.toNat_mul] using h

end LocalLength
end Module
