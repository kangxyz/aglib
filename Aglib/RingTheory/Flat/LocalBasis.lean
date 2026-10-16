/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# Local bases for finitely presented flat modules

At each prime, a finitely presented flat module has an actual finite basis
after inverting one element outside that prime. The ring and module retain
the original universe; the algebra corollary retains finite presentation.

Source: `R5Lab/AlgebraicGeometry/Curves/Degree/FiniteFlatLocallyFree.lean`, frozen R5 integration
`79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`d3dc4d7ca161eb1493165b50730ef4e573da5882fd475b4d4d520c066d42a7fb`. Selected original ranges: [[151,
174]].
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open Module
universe u

theorem Module.FinitePresentation.exists_basis_away_of_flat
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [Module.Flat R M] (p : PrimeSpectrum R) :
    ∃ r : R, r ∉ p.asIdeal ∧ ∃ n : ℕ,
      Nonempty (Basis (Fin n) (Localization.Away r) (LocalizedModule.Away r M)) := by
  letI : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis (Localization.AtPrime p.asIdeal)
    (LocalizedModule p.asIdeal.primeCompl M)
  obtain ⟨r, hr, b', -⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
    (Localization.AtPrime p.asIdeal) b
  exact ⟨r, hr, _, ⟨b'⟩⟩

theorem Algebra.FinitePresentation.exists_moduleBasis_away_of_flat
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.FinitePresentation R A] [Module.Flat R A]
    (p : PrimeSpectrum R) :
    ∃ r : R, r ∉ p.asIdeal ∧ ∃ n : ℕ,
      Nonempty (Basis (Fin n) (Localization.Away r) (LocalizedModule.Away r A)) := by
  letI : Module.FinitePresentation R A :=
    Module.FinitePresentation.of_finite_of_finitePresentation R A
  exact Module.FinitePresentation.exists_basis_away_of_flat R A p
