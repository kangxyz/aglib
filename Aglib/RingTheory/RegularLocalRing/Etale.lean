/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Ideal.GoingDown

/-!
# Essentially etale local maps

A local map of Noetherian local rings that is essentially of finite type,
flat, and formally unramified preserves local Krull dimension and carries
regular local rings to regular local rings. The proof uses the maximal-ideal
identity, going-down height formula, and a bound on generators.

## Extraction basis

Transferred from `R5Lab.RingTheory.RegularLocalRing.Etale` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`5f9a38edf67583b89fe22d3eadbbe842f0c1b40bd26edc6c47b5df0bafcfe343`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

namespace Algebra.FormallyUnramified

open IsLocalRing

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalHom (algebraMap R S)] [EssFiniteType R S]
    [Module.Flat R S] [FormallyUnramified R S]

/-- An essentially finite type, flat, formally unramified local map preserves
local Krull dimension. -/
theorem ringKrullDim_eq_of_flat : ringKrullDim S = ringKrullDim R := by
  have hmap := FormallyUnramified.map_maximalIdeal (R := R) (S := S)
  have hheight := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (maximalIdeal R) (maximalIdeal S)
  rw [hmap, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at hheight
  simpa using congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) hheight

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Regularity ascends along an essentially finite type, flat, formally
unramified local map. -/
theorem isRegularLocalRing_of_flat [IsRegularLocalRing R] : IsRegularLocalRing S := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [← FormallyUnramified.map_maximalIdeal (R := R) (S := S),
    ringKrullDim_eq_of_flat R S, ← IsRegularLocalRing.spanFinrank_maximalIdeal]
  exact WithBot.coe_le_coe.mpr <| by
    exact_mod_cast Ideal.spanFinrank_map_le_of_fg (algebraMap R S)
      (IsNoetherian.noetherian (maximalIdeal R))

end Algebra.FormallyUnramified
