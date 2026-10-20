/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Conditional proper-birational DVR isomorphism locus

This is the exact general theorem-family input used by the DVR recognition consumer.
It is a proposition type, with no supplier asserted in this leaf. The actual function-field
map is the native generic-stalk map, with the same contravariant direction as the source.

Selected source: `R5Lab/Aglib/AlgebraicGeometry/Morphisms/Proper/BirationalInterfaces.lean`,
R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`150d0c411e909cb01dfc6df85d20fb12c3a5db18797b35882c4ac67b3ec87b6c`.
The independent connected-fibre theorem-family predicate is outside this consumer cut.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- The general proper-birational isomorphism-locus statement at an actual DVR stalk.
Local Noetherianity of the target, properness, dominance and the actual function-field
isomorphism are all explicit. This declaration does not prove the theorem family. -/
def ProperBirationalDVRIsomorphismLocus : Prop :=
  ∀ (X Y : Scheme.{u}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f],
    IsIso (CommRingCat.ofHom (functionFieldMap f)) →
      ∀ (y : Y) [IsDiscreteValuationRing (Y.presheaf.stalk y)],
        ∃ U : Y.Opens, y ∈ U ∧ IsIso (f ∣_ U)

end AlgebraicGeometry.Scheme
