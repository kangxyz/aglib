/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Generic points under surjective scheme maps

A surjective morphism between arbitrary irreducible schemes maps the
actual generic point to the actual generic point. No integral, finite,
proper, Noetherian, or dimension hypothesis occurs.

Source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.ProperCurveFiniteness`, R5 revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`. The native declaration retains
the hypotheses, universes, actual maps and proof.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Order
universe u
namespace AlgebraicGeometry.Scheme

/-- A surjective scheme morphism between irreducible schemes preserves generic points. -/
theorem map_genericPoint_of_surjective (Y X : Scheme.{u}) [IrreducibleSpace Y] [IrreducibleSpace X]
    (f : Y ⟶ X) [Surjective f] : f (genericPoint Y) = genericPoint X := by
  obtain ⟨y, hy⟩ := f.surjective (genericPoint X)
  have h : f (genericPoint Y) ⤳ genericPoint X := by
    simpa only [hy] using (genericPoint_specializes y).map f.continuous
  exact (h.antisymm (genericPoint_specializes _)).eq


end AlgebraicGeometry.Scheme

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/Morphisms/Surjective/GenericPoint.lean
SHA-256 0247080777b421e34cbcd5a34641217d81a21ad1c6defe65d88b328858c73a51. -/
