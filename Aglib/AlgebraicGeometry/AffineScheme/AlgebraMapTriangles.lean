/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Structural triangles for algebra maps on spectra

The three source structural triangles use the same actual scalar map. Their
common implementation has no field, DVR or finiteness assumption.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Spec

universe u

/-- The spectrum of an algebra homomorphism commutes with the actual scalar maps. -/
@[reassoc] theorem map_algHom_algebraMap {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.algebraMap R A =
      Spec.algebraMap R B := by
  rw [Spec.algebraMap, Spec.algebraMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact f.comp_algebraMap

end AlgebraicGeometry.Spec

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/AffineScheme/AlgebraMapTriangles.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 bfafd60ba1bd468b735b110eb24a9a6b54ac9288a2e452a0f7e949138db5ac6c. -/
