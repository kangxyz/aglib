/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.GenericFreeness.Noetherian
public import Mathlib.RingTheory.Unramified.Finite

/-!
# Generic finiteness of unramified algebras

A finite-type formally unramified algebra over a Noetherian domain becomes
finite after one nonzero base localization. The algebra is the literal tensor
base change, including when the original algebra is zero. Generic freeness is
applied to the algebra itself; an unramified free algebra is finite.
-/

@[expose] public section

open scoped TensorProduct

namespace Algebra.FormallyUnramified

variable {A C : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
  [CommRing C] [Algebra A C] [Algebra.FiniteType A C] [Algebra.FormallyUnramified A C]

/-- A finite-type formally unramified algebra is finite on a nonempty principal
open of a Noetherian integral base. No nontriviality of the algebra is required. -/
theorem exists_ne_zero_finite_baseChange :
    ∃ a : A, a ≠ 0 ∧
      Module.Finite (Localization.Away a) ((Localization.Away a) ⊗[A] C) := by
  obtain ⟨a, ha, hfree⟩ :=
    Module.Finite.exists_ne_zero_free_localizedModule_away (A := A) (B := C) C
  let := hfree
  let : Module.Free (Localization.Away a) ((Localization.Away a) ⊗[A] C) :=
    Module.free_of_isLocalizedModule_of_free_isLocalizedModule
      (Submonoid.powers a) (Localization.Away a)
      (LocalizedModule.mkLinearMap (Submonoid.powers a) C)
      (TensorProduct.mk A (Localization.Away a) C 1)
  exact ⟨a, ha, finite_of_free (Localization.Away a) ((Localization.Away a) ⊗[A] C)⟩

end Algebra.FormallyUnramified
