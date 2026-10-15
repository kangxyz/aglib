/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Locally constant fibre dimensions of finitely presented flat modules

The native stalk-rank theorem identifies the original residue-field fibre
dimension of a finitely presented flat module with its locally constant
stalk rank. This comparison is used termwise for finite perfect complexes;
no Noetherian or global freeness hypothesis is needed.
-/

@[expose] public section

noncomputable section

open Module

namespace Module

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [Module.Flat R M]

/-- The original residue-field fibre dimension of a finitely presented flat module is
locally constant. The ring and module universes are independent. -/
theorem isLocallyConstant_finrank_fiber :
    IsLocallyConstant (fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M)) := by
  have he : (fun p : PrimeSpectrum R => finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M)) =
      rankAtStalk (R := R) M :=
    funext fun p => (rankAtStalk_eq (R := R) (M := M) p).symm
  rw [he]
  exact isLocallyConstant_rankAtStalk

end Module
