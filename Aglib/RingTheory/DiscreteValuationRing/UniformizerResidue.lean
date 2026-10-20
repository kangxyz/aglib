/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Residue of uniformizers and their positive powers

Source: R5 baseline `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Existing declarations, chosen maps and explicit evidence boundaries are preserved.
-/

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/DiscreteValuationRing/UniformizerResidue.lean`
at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`c771ff2189fc3fec15c9154c0f192c407183ea6c6f065763c38b6fea7ad89cfe`.
-/

@[expose] public section

open IsLocalRing
universe u

namespace IsDiscreteValuationRing

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

lemma uniformizer_residue_zero (π : R) (hπ : Irreducible π) : residue R π = 0 :=
  (residue_eq_zero_iff π).mpr hπ.not_isUnit

end IsDiscreteValuationRing

namespace IsDiscreteValuationRing

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

lemma power_residue_zero (π : R) (hπ : Irreducible π) (m : ℕ) (hm : 0 < m) :
    residue R (π^m) = 0 := by
  simp [map_pow, uniformizer_residue_zero π hπ, hm.ne']

end IsDiscreteValuationRing
