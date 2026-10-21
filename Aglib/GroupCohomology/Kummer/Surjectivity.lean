/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupCohomology.Kummer.PrimeToCharacteristic

/-!
# Characteristic-zero Kummer surjectivity

For a field of characteristic zero, every actual continuous roots-of-unity cocycle has a
unit/root representative at every natural level. The actual Kummer class map is surjective at
positive levels. These results specialize the perfect-field route through exactly the same
base-unit map, cocycle and Kummer class.

Extraction source: `R5Lab.Aglib.GroupCohomology.Kummer.Surjectivity`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`1717b468026d3ebf27c81973c57ae78e884285e14485d686080994996a7f7959`.
The source conditions, actual objects and canonical maps are retained under native names.
-/

@[expose] public section

noncomputable section

namespace GroupCohomology.Kummer

open Field.absoluteGaloisGroup.RootsOfUnity _root_.GroupCohomology.ContinuousH1

variable (K : Type*) [Field K] [CharZero K] (n : ℕ)

/-- Over a characteristic-zero field, every actual continuous roots-of-unity cocycle
is the Kummer cocycle of a base-field unit, with equality of representatives. -/
theorem exists_unit_cocycle
    (c : Cocycle (Field.absoluteGaloisGroup K) (Mu K n)) :
    ∃ (u : Kˣ) (β : (AlgebraicClosure K)ˣ) (hβ : β ^ n = baseUnits K u),
      cocycle K n β hβ = c :=
  exists_unit_cocycle_of_perfect K n c

/-- The same actual continuous Kummer map is surjective in characteristic zero
at every positive level. -/
theorem kummer_surjective (hn : 0 < n) : Function.Surjective (kummer K n hn) :=
  kummer_surjective_of_perfect K n hn

end GroupCohomology.Kummer
