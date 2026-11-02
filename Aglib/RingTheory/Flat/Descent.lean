/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHomProperties

/-!
# Flat ring maps descend along faithfully flat base change

The original tensor-product descent theorem for modules supplies the
native `RingHom.CodescendsAlong` property. The base change and comparison
maps are those of that existing constructor.
-/

@[expose] public section

namespace RingHom

/-- Flatness of the original ring map descends along faithfully flat
base change, using the actual scalar-extension tensor product. -/
theorem Flat.codescendsAlong_faithfullyFlat : CodescendsAlong Flat FaithfullyFlat := by
  refine .mk _ Flat.respectsIso fun R S T _ _ _ _ _ h h' => ?_
  rw [flat_algebraMap_iff] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  let := h
  let := h'
  exact Module.Flat.of_flat_tensorProduct R T S

end RingHom
