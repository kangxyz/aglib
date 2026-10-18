/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Coefficient morphisms of actual polynomial projective spaces

The morphism is Mathlib's `Proj.map` of the native graded polynomial coefficient
map. Its identity, composition and exact inverse images of standard coordinate
opens are proved over arbitrary commutative rings. Two factorizations of one ring
map give the same composite (`map_comp_map_eq_of_comp_eq`).
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The actual projective coefficient morphism induced by the original ring homomorphism. -/
def map (f : R →+* S) (ι : Type u) : ProjectiveSpace S ι ⟶ ProjectiveSpace R ι :=
  Proj.map (MvPolynomial.gradedMap f) (by rw [MvPolynomial.irrelevant_map_gradedMap])

@[simp]
theorem map_id (ι : Type u) : map (RingHom.id R) ι = 𝟙 (ProjectiveSpace R ι) := by
  simpa only [map, MvPolynomial.gradedMap_id] using
    (Proj.map_id (𝒜 := MvPolynomial.homogeneousSubmodule ι R))

/-- The actual projective morphism reverses composition of the original coefficient maps. -/
theorem map_comp (g : S →+* T) (f : R →+* S) (ι : Type u) :
    map (g.comp f) ι = map g ι ≫ map f ι := by
  simpa only [map, MvPolynomial.gradedMap_comp] using
    (Proj.map_comp (MvPolynomial.gradedMap (ι := ι) f) (MvPolynomial.gradedMap g)
      (MvPolynomial.irrelevant_map_gradedMap f).ge (MvPolynomial.irrelevant_map_gradedMap g).ge)

/-- Projective coefficient maps of two factorizations of one ring map agree:
`g.comp f = g'.comp f'` gives `map g ι ≫ map f ι = map g' ι ≫ map f' ι`. -/
theorem map_comp_map_eq_of_comp_eq {A : Type u} [CommRing A] (ι : Type u)
    {B B' C : Type u} [CommRing B] [CommRing B'] [CommRing C] {f : A →+* B} {g : B →+* C}
    {f' : A →+* B'} {g' : B' →+* C} (h : g.comp f = g'.comp f') :
    map g ι ≫ map f ι = map g' ι ≫ map f' ι := by
  rw [← map_comp, h, map_comp]

/-- The inverse image of an original standard coordinate chart is exactly the same chart
over the new coefficient ring. -/
@[simp]
theorem map_preimage_coordinateOpen (f : R →+* S) (ι : Type u) (i : ι) :
    map f ι ⁻¹ᵁ coordinateOpen R ι i = coordinateOpen S ι i := by
  simp [map, coordinateOpen, Proj.map_preimage_basicOpen]

end AlgebraicGeometry.ProjectiveSpace
