/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.GlobalSections

/-!
# Original homogeneous sections in native Laurent H0

The actual homogeneous polynomial section has the original polynomial as its Laurent
coordinate on every tuple intersection. Its original degree-zero augmentation therefore
has exactly those coefficients under the existing global-section comparison.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Cech Opposite MvPolynomial
open AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The restriction of an original homogeneous global section has the original polynomial
as its exact Laurent coordinate on each categorical tuple intersection. -/
theorem twistingTupleSectionsLinearEquiv_homogeneousSection (m : ℕ)
    (p : homogeneousSubmodule ι R m) (q : ℕ) (a : Fin (q + 1) → ι) :
    (twistingTupleSectionsLinearEquiv R ι (m : ℤ) q a
        ((twistingSheaf R ι (m : ℤ)).val.map (homOfLE le_top).op
          (homogeneousSection R ι m p))).val =
      toCoordinateLaurent R (coordinateTupleSet a) p.val := by
  let e := eqToIso (coordinateTupleOpen_eq R ι q a).symm
  change (twistingSectionsLaurentAddEquiv R ι (coordinateTupleSet a) (a 0)
      ((mem_coordinateTupleSet a (a 0)).mpr ⟨0, rfl⟩) (m : ℤ)
      ((twistingSheaf R ι (m : ℤ)).val.map e.hom.op
        ((twistingSheaf R ι (m : ℤ)).val.map (homOfLE le_top).op
          (homogeneousSection R ι m p)))).val = _
  rw [← PresheafOfModules.map_comp_apply]
  exact twistingSectionsLaurentAddEquiv_homogeneousSection R ι (coordinateTupleSet a)
    (a 0) ((mem_coordinateTupleSet a (a 0)).mpr ⟨0, rfl⟩) m p

/-- The native zero-term embedding of the original homogeneous section class has exactly
the original Laurent polynomial on each one-coordinate tuple. -/
theorem twistingGlobalSectionsLaurentZeroLinearEquiv_homogeneousSection (m : ℕ)
    (p : homogeneousSubmodule ι R m) (a : Fin 1 → ι) :
    (CochainComplex.homologyZeroι (coordinateLaurentTupleComplex (ι := ι) R (m : ℤ))
        (twistingGlobalSectionsLaurentZeroLinearEquiv R ι (m : ℤ)
          (homogeneousSection R ι m p)) a).val =
      toCoordinateLaurent R (coordinateTupleSet a) p.val := by
  rw [twistingGlobalSectionsLaurentZeroLinearEquiv_component]
  exact twistingTupleSectionsLinearEquiv_homogeneousSection R ι m p 0 a

end AlgebraicGeometry.Scheme.Cohomology
