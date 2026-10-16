/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Bases of standard smooth Kähler differential modules

A native standard smooth presentation of relative dimension `n` supplies a
basis indexed by `Fin n` of the actual Kähler differential module. The rings
may have different universes; no field or scheme hypothesis is used.

Extracted without changing the basis or proof from
`Scheme.Modules.Differentials.SmoothRank.standardSmoothDifferentialBasis`.
The older name delegates to this sole ring-theoretic implementation.
Its source is `R5Lab/AlgebraicGeometry/Curves/Differentials/SmoothRank.lean`
at frozen R5 integration `79307ff88f07d34fd5c3edb859f799c55e38f290`,
SHA-256 `bab90251fd10024bc7477d90539648aa6b08e4047f6d288f0e755b0b852443b5`.
-/

@[expose] public section

noncomputable section

namespace KaehlerDifferential

universe u v

-- Preserve the source proof and its local instance binders during the owner extraction.
set_option linter.style.haveILetI false in
/-- A standard smooth presentation of relative dimension `n` supplies a basis of its
actual Kähler differential module. -/
def standardSmoothBasis
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    Module.Basis (Fin n) S Ω[S⁄R] := by
  classical
  exact Classical.choice (show Nonempty (Module.Basis (Fin n) S Ω[S⁄R]) from by
    obtain ⟨ι, σ, hσ, hι, P, hP⟩ :=
      (inferInstance : Algebra.IsStandardSmoothOfRelativeDimension n R S).out
    letI : Finite ι := hι
    letI : Finite σ := hσ
    letI : Fintype ι := Fintype.ofFinite ι
    letI : Fintype σ := Fintype.ofFinite σ
    have hc : Fintype.card ((Set.range P.map)ᶜ : Set ι) = n := by
      rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj]
      simpa only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card] using hP
    exact ⟨P.basisKaehler.reindex (Fintype.equivFinOfCardEq hc)⟩)

end KaehlerDifferential
