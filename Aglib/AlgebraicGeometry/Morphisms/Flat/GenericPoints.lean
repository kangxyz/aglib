/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Generic points under flat maps

The complete generalizing-map proof lives at the flat-morphism layer. The
existing public declaration name is retained for compatibility; its statement
and proof have no curve, cohomology, or finiteness hypotheses.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Set

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

variable (X : Scheme.{u})

/-- A component-generic point is maximal in the scheme's specialization order. -/
theorem genericPoint_isMax (η : genericPoints X) : IsMax η.val := by
  intro x hx
  change η.val ⤳ x
  exact specializes_iff_closure_subset.mpr
    (η.property.2 isIrreducible_singleton.closure hx.closure_subset)

/-- A maximally general point of a scheme is a component-generic point. -/
theorem mem_genericPoints_of_isMax (X : Scheme.{u}) (x : X) (hx : IsMax x) :
    x ∈ genericPoints X := by
  obtain ⟨Z, hZ, hxZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({x} : Set X)) isIrreducible_singleton.closure
  let η := genericPoints.ofComponent ⟨Z, hZ⟩
  have hη : η.val ⤳ x :=
    (isGenericPoint_iff_specializes.mp (genericPoints.isGenericPoint_ofComponent ⟨Z, hZ⟩) x).mpr
      (hxZ (subset_closure (mem_singleton x)))
  have he : η.val = x := (hη.antisymm (hx hη)).eq
  exact he ▸ η.property

/-- Flat maps carry actual component-generic points to component-generic points. -/
theorem genericPoint_map_flat {U X : Scheme.{u}} (f : U ⟶ X) [Flat f]
    (η : genericPoints U) : f η.val ∈ genericPoints X := by
  apply mem_genericPoints_of_isMax
  intro y hy
  change f η.val ⤳ y
  obtain ⟨z, hz, hfz⟩ := Flat.generalizingMap f (show y ⤳ f η.val from hy)
  have h := (genericPoint_isMax U η hz).map f.continuous
  simpa only [hfz] using h

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
