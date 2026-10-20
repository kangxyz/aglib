/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.GenericFiber
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# The fraction-field spectrum as a DVR principal open

The actual fraction-ring algebra map of a discrete valuation ring is localization
away from an irreducible uniformizer. Its spectrum map is therefore an open immersion.

Source: `R5Lab/Aglib/AlgebraicGeometry/FunctionField/DVRGenericOpen.lean`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, lines 30–45, SHA-256
`cf8efff7a5e7476f053006c2417fc94f7d69e90b0759fcc739f004778ba4cef3`.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.LocalRing.GenericFiber

variable {R F : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- The actual fraction-field spectrum of a DVR is its uniformizer principal open. -/
theorem baseMap_isOpenImmersion : IsOpenImmersion (baseMap R F) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hloc : IsLocalization.Away π F := by
    apply (IsLocalization.iff_of_le_of_exists_dvd (S := F)
      (M := Submonoid.powers π) (nonZeroDivisors R) ?_ ?_).mpr
    · infer_instance
    · rintro x ⟨n, rfl⟩
      exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hπ.ne_zero)
    · intro x hx
      obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
        (mem_nonZeroDivisors_iff_ne_zero.mp hx) hπ
      exact ⟨π ^ n, ⟨n, rfl⟩, hn.dvd⟩
  let := hloc
  exact IsOpenImmersion.of_isLocalization π

end AlgebraicGeometry.Scheme.LocalRing.GenericFiber
