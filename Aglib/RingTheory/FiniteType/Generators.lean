/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Surjectivity from algebra generators

The actual range of a ring map is all of its target when it contains the
coefficient ring and a set of algebra generators. No finiteness or reducedness
assumption is needed for this range criterion.
-/

@[expose] public section

namespace RingHom

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]

/-- A ring map containing the coefficients and algebra generators is surjective. -/
theorem surjective_of_adjoin_eq_top (f : B →+* A) (k : R →+* B)
    (hk : f.comp k = algebraMap R A) (s : Set A)
    (hs : Algebra.adjoin R s = ⊤) (hfs : s ⊆ Set.range f) :
    Function.Surjective f := by
  let T : Subalgebra R A :=
    { f.rangeS with
      algebraMap_mem' := fun r => ⟨k r, DFunLike.congr_fun hk r⟩ }
  have hT : Algebra.adjoin R s ≤ T := Algebra.adjoin_le hfs
  rw [hs] at hT
  intro a
  exact hT (show a ∈ (⊤ : Subalgebra R A) from trivial)

end RingHom
