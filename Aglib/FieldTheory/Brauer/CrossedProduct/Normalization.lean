/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Normalizing native multiplicative two-cocycles

Normalization divides by the coboundary of the constant identity value.
A primitive for the normalized cocycle gives a primitive for the original one,
with the native multiplicative coboundary convention unchanged.
-/

@[expose] public section

namespace groupCohomology

variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-- Normalize a multiplicative two-cochain at its identity value. -/
def normalize₂ (c : G × G → M) (p : G × G) : M := c p / p.1 • c (1, 1)

/-- Normalization preserves the native cocycle equation. -/
theorem IsMulCocycle₂.normalize {c : G × G → M} (hc : IsMulCocycle₂ c) :
    IsMulCocycle₂ (normalize₂ c) := by
  intro g h j
  simp only [normalize₂, smul_div', div_mul_div_comm, mul_smul]
  rw [hc g h j]

@[simp]
theorem normalize₂_one_one (c : G × G → M) : normalize₂ c (1, 1) = 1 := by
  simp [normalize₂]

/-- Undoing normalization transports an actual primitive, not just a quotient class. -/
theorem isMulCoboundary₂_of_normalize {c : G × G → M}
    (hc : IsMulCoboundary₂ (normalize₂ c)) : IsMulCoboundary₂ c := by
  obtain ⟨b, hb⟩ := hc
  refine ⟨fun g => b g * c (1, 1), ?_⟩
  intro g h
  calc
    g • (b h * c (1, 1)) / (b (g * h) * c (1, 1)) * (b g * c (1, 1)) =
        (g • b h / b (g * h) * b g) * g • c (1, 1) := by
          simp [smul_mul', div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    _ = c (g, h) := by rw [hb]; exact div_mul_cancel _ _

end groupCohomology
