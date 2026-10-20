/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.Rank

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/
/-!
# Affine finite étale rank

Actual module-localization rank, local constancy, connected constancy, tensor
base change and surjectivity positivity. No general theorem premises.
Application: K2-018#prop:k2018-arithmetic-characters, historical source
 e73d98b1b5c1e5abcdebf7d058e436d792b87982, expose.tex lines341–445;
engineering7f86e4a1763cc4ec35e9b0a8acd659750355a0de and frozen pins.
-/

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Affine` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`e5f9fd4700521ae41a89682e41643c6bab5a5945d831e42f005bf0cc2c61073c`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option linter.style.haveILetI false
open Algebra TensorProduct
namespace Algebra.FiniteEtaleRank
universe u v w
variable (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
  [Module.Finite R A] [Algebra.Etale R A]

/-- The genuine affine module rank is locally constant for finite étale algebras. -/
theorem rank_locallyConstant :
    IsLocallyConstant (Module.rankAtStalk (R := R) A) := by
  letI : Module.FinitePresentation R A :=
    Module.FinitePresentation.of_finite_of_finitePresentation R A
  exact Module.isLocallyConstant_rankAtStalk

/-- Connectedness, including nonemptiness, makes affine finite étale rank constant. -/
theorem exists_constant_rank [ConnectedSpace (PrimeSpectrum R)] :
    ∃ n : ℕ, ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) A p = n := by
  obtain ⟨p⟩ := (inferInstance : Nonempty (PrimeSpectrum R))
  exact ⟨_, fun q ↦ (rank_locallyConstant R A).apply_eq_of_preconnectedSpace q p⟩

/-- Actual tensor-product base change preserves affine local rank. -/
theorem rank_baseChange
    (S : Type w) [CommRing S] [Algebra R S] (p : PrimeSpectrum S) :
    Module.rankAtStalk (R := S) (S ⊗[R] A) p =
      Module.rankAtStalk (R := R) A (p.comap (algebraMap R S)) :=
  Module.rankAtStalk_baseChange (M := A) p

/-- Surjectivity on the actual affine prime spectra makes every local rank positive. -/
theorem rank_pos_of_surjective
    (hs : Function.Surjective (PrimeSpectrum.comap (algebraMap R A)))
    (p : PrimeSpectrum R) : 0 < Module.rankAtStalk (R := R) A p :=
  PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective.mpr hs p
end Algebra.FiniteEtaleRank
