/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Local and Noetherian trivial square-zero extensions

Let `R` be a commutative ring and `M` an `R`-module, with the central right action that
Mathlib's `TrivSqZeroExt R M = R ⊕ M` uses.

* If `R` is local, so is `R ⊕ M` (`TrivSqZeroExt.isLocalRing`): an element is a unit exactly
  when its first coordinate is (Mathlib's `TrivSqZeroExt.isUnit_iff_isUnit_fst`). The first
  projection `R ⊕ M → R` is then a local homomorphism (`TrivSqZeroExt.isLocalHom_fstHom`).
* If `R` is Noetherian and `M` is finite over `R`, then `R ⊕ M` is Noetherian
  (`TrivSqZeroExt.isNoetherianRing`): it is a finite `R`-module.

For a field `L`, these apply to `L[ε] = TrivSqZeroExt L L` (Mathlib proves its locality as
`DualNumber`'s instance in `Mathlib.RingTheory.DualNumber`) and to `L[ε, ε'] =
TrivSqZeroExt L (L × L)`. They make `Spec (L ⊕ M)` a local, locally Noetherian test scheme.
-/

@[expose] public section

namespace TrivSqZeroExt

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
  [IsCentralScalar R M]

/-- A trivial square-zero extension of a local ring is local. -/
instance isLocalRing [IsLocalRing R] : IsLocalRing (TrivSqZeroExt R M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simpa only [isUnit_iff_isUnit_fst, fst_sub, fst_one] using
      IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst

/-- The first projection of a trivial square-zero extension is a local homomorphism. -/
instance isLocalHom_fstHom (S : Type*) [CommSemiring S] [Algebra S R] [Module S M]
    [IsScalarTower S R M] [IsScalarTower S Rᵐᵒᵖ M] : IsLocalHom (fstHom S R M) :=
  ⟨fun _ ha => isUnit_iff_isUnit_fst.mpr ha⟩

/-- A trivial square-zero extension of a Noetherian ring by a finite module is Noetherian. -/
instance isNoetherianRing [IsNoetherianRing R] [Module.Finite R M] :
    IsNoetherianRing (TrivSqZeroExt R M) := by
  have : Module.Finite R (TrivSqZeroExt R M) := inferInstanceAs (Module.Finite R (R × M))
  exact isNoetherian_of_tower R (isNoetherian_of_isNoetherianRing_of_finite R _)

end TrivSqZeroExt
