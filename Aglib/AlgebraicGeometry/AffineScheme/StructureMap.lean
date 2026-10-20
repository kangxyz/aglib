/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AffineScheme.AlgebraMapTriangles
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Structure maps of affine algebras over a field

The structure map is the native `Spec.algebraMap`. Its finite-type property
uses the actual finite-type algebra structure. Structural triangles are in
`AlgebraMapTriangles` and require only commutative rings.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace AlgebraicGeometry.Spec

universe u

/-- A finite-type algebra over a field has a locally finite-type affine structure map. -/
instance algebraMap_locallyOfFiniteType {k A : Type u} [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] : LocallyOfFiniteType (Spec.algebraMap k A) := by
  apply HasRingHomProperty.Spec_iff.mpr
  exact RingHom.finiteType_algebraMap.mpr inferInstance

end AlgebraicGeometry.Spec

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/AffineScheme/StructureMap.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 98140ad68c3b761262081ba05519514a78860e236860577591b7a1403250957a. -/
