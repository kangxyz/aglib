/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.Cup
public import Aglib.AlgebraicGeometry.Geometrically.Integral.GlobalSections

/-!
# Connectedness of the coherent cohomology algebra

For a proper geometrically integral field scheme, scalar multiples of the
original cup unit are exactly its degree-zero cohomology. The map is the
actual structural constants map through the existing degree-zero section
comparison. This supplies the connectedness needed by proper group
cohomology; topological connectedness alone is not substituted for it.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {k : Type u} [Field k] (X : FScheme k)
  [IsProper X.hom] [GeometricallyIntegral X.hom]

/-- Scalar multiples of the original cup unit give all degree-zero
cohomology, with the actual structural scalar action. -/
theorem exists_smul_cupUnit_eq (x : structureCohomology k X 0) :
    ∃ a : k, a • structureCupUnit X = x := by
  let := globalSectionsModule X
  obtain ⟨a, ha⟩ := (constants_bijective_of_proper_geometricallyIntegral X).surjective
    (structureH0Equiv X x)
  refine ⟨a, (structureH0Equiv X).injective ?_⟩
  rw [map_smul, structureH0Equiv_cupUnit]
  change constants X a * 1 = structureH0Equiv X x
  simpa only [mul_one] using ha

/-- The actual structural scalar map to degree-zero cohomology is
bijective; this is the connected grading map needed in the Hopf argument. -/
theorem smul_cupUnit_bijective :
    Function.Bijective (fun a : k => a • structureCupUnit X) := by
  let := globalSectionsModule X
  refine ⟨?_, exists_smul_cupUnit_eq X⟩
  intro a b h
  have hs := congrArg (structureH0Equiv X) h
  simp only [map_smul, structureH0Equiv_cupUnit] at hs
  apply (constants_bijective_of_proper_geometricallyIntegral X).injective
  change constants X a * 1 = constants X b * 1 at hs
  simpa only [mul_one] using hs

/-- Canonical scalar identification of the actual degree-zero coherent
cohomology of a proper geometrically integral scheme. -/
def structureH0ScalarEquiv : k ≃ₗ[k] structureCohomology k X 0 :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton k _ (structureCupUnit X))
    (smul_cupUnit_bijective X)

@[simp]
theorem structureH0ScalarEquiv_apply (a : k) :
    structureH0ScalarEquiv X a = a • structureCupUnit X := rfl

theorem structureH0ScalarEquiv_one :
    structureH0ScalarEquiv X 1 = structureCupUnit X := by
  simp

end AlgebraicGeometry.Scheme.Cohomology
