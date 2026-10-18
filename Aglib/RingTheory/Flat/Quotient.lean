/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Flatness through the actual surjective quotient map

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`, SHA-256
  `79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `docs/WORK_PLAN.md` and
the migration records; the source hashes above identify extraction inputs.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open LinearMap

section
namespace RingHom

/-- A surjective quotient map transports flatness of its actual kernel quotient. -/
theorem flat_comp_of_flat_quotient {R A B : Type*}
    [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B) (hg : Function.Surjective g)
    (I : Ideal A) (hI : RingHom.ker g = I)
    (hflat : let := f.toAlgebra; Module.Flat R (A ⧸ I)) :
    (g.comp f).Flat := by
  subst I
  let := f.toAlgebra
  let := g.toAlgebra
  let := (g.comp f).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let e : (A ⧸ RingHom.ker g) ≃ₐ[R] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := IsScalarTower.toAlgHom R A B) hg
  have : Module.Flat R (A ⧸ RingHom.ker g) := hflat
  change Module.Flat R B
  exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv

end RingHom
end
