/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalPoint.Basic
public import Mathlib.Algebra.CharP.Algebra

/-!
# Residue units and characteristic at actual rational points

Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.RationalSectionResidue`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`,
SHA-256 `134c4ea7aa69096267a16db0e9395d6ebcdef6b4089a840d50f96e7261993379`, selected lines [[18,
29], [35, 49]].
The actual scheme objects, canonical maps, universes and conditions are retained.
-/

@[expose] public section

noncomputable section
open AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.RationalPoint
variable {F : Type u} [Field F] {X : Scheme.{u}} (q : RationalPoint F X)

include q in
/-- The actual constants embedding transfers characteristic zero to the generic stalk. -/
theorem functionField_charZero [IsIntegral X] [CharZero F] : CharZero X.functionField :=
  charZero_of_injective_ringHom (q.functionFieldConstants).injective

/-- The rational section's canonical residue equivalence on actual residue-field units. -/
def residueUnitsMap : (IsLocalRing.ResidueField q.localRing)ˣ →* Fˣ :=
  Units.map q.residueEquiv.toRingHom.toMonoidHom

/-- Transport by the actual residue equivalence preserves minus one. -/
theorem residueUnitsMap_neg_one : q.residueUnitsMap (-1) = -1 := by
  apply Units.ext
  change q.residueEquiv.toRingHom (-1) = -1
  rw [map_neg, map_one]

/-- Nonzero natural levels are units in the actual stalk over a characteristic-zero field. -/
theorem level_isUnit [CharZero F] (n : ℕ) [NeZero n] : IsUnit (n : q.localRing) := by
  have hn : (n : F) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  simpa only [map_natCast] using q.constants_isUnit hn

end AlgebraicGeometry.Scheme.RationalPoint
