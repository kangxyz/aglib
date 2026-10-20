/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.CharP.Algebra

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/Units/PositiveNat.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`50cb8a5289c761d6a3916575066fa92e5a7b383b091d78ab13f207ac5eb1f454`.
-/

@[expose] public section

namespace Algebra
universe u
/-- The finite-comparison invertibility condition holds on every local
F-algebra in the schema, through its actual constants map. -/
theorem isUnit_natCast_of_pos (F R : Type u) [Field F] [CharZero F] [CommRing R]
    (i : F →+* R) (n : ℕ) [NeZero n] : IsUnit (n : R) := by
  have hn : IsUnit (n : F) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne n))
  simpa only [map_natCast] using hn.map i

end Algebra
