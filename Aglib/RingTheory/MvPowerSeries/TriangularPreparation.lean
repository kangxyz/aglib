/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPowerSeries.WeierstrassNormalization
public import Aglib.RingTheory.MvPowerSeries.AdicComplete

/-!
# Weierstrass preparation after triangular normalization

Over a complete Noetherian local ring, every series nonzero over the residue
field admits Weierstrass preparation after an actual triangular coordinate
automorphism. Completeness of the iterated coefficient ring is supplied for
its mixed maximal ideal, not assumed as an additional power-series hypothesis.
This is formal preparation only; it does not identify algebraic power series
with a henselization or prove Artin approximation.
-/

@[expose] public section

namespace MvPowerSeries

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- Formal preparation after a triangular change, over arbitrary residue fields. -/
theorem exists_triangular_isWeierstrassFactorization (n : ℕ)
    (f : MvPowerSeries (Fin (n + 1)) R)
    (hf : map (IsLocalRing.residue R) f ≠ 0) :
    ∃ (w : Fin (n + 1) → ℕ) (hw : ∀ i, 0 < w i),
      w (Fin.last n) = 1 ∧
      ∃ (P : Polynomial (MvPowerSeries (Fin n) R))
        (u : PowerSeries (MvPowerSeries (Fin n) R)),
        (finLastEquiv R n
          (triangularAlgEquiv (Fin.last n) w (fun i _ ↦ hw i) f)).IsWeierstrassFactorization
            P u := by
  let : IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) R))
      (MvPowerSeries (Fin n) R) := isAdicComplete_maximalIdeal (Fin n) R
  obtain ⟨w, hw, hp, hne⟩ := exists_triangular_map_residue_ne_zero n f hf
  exact ⟨w, hw, hp, PowerSeries.exists_isWeierstrassFactorization hne⟩

end MvPowerSeries
