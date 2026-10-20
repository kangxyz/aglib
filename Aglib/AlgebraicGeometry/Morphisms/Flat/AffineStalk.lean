/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange

/-!
# Flatness of actual affine germs

An affine germ is a canonical localization. The already native
`Scheme.fromSpecStalk_flat` supplies flatness of the canonical stalk spectrum map.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace AlgebraicGeometry.IsAffineOpen

universe u

/-- An actual affine germ is a localization, hence its Spec map is flat.
The localization identification is mathlib d13f23b723b8a846827a245b89c10fc7d3f11612,
`AlgebraicGeometry/AffineScheme.lean:833`, applied with the literal germ algebra.
Flatness uses `RingTheory/Flat/Localization.lean:37` and `Flat.SpecMap_iff`. -/
theorem flat_specMap_germ {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U) : Flat (Spec.map (X.presheaf.germ U x hx)) := by
  apply Flat.SpecMap_iff.mpr
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  have := hU.isLocalization_stalk ⟨x, hx⟩
  exact IsLocalization.flat (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl

end AlgebraicGeometry.IsAffineOpen

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/Morphisms/Flat/AffineStalk.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 12cdd1107624c04cedc9af9032bfd4eb594d928954885f6e4e7fd005bb280aa2. -/
