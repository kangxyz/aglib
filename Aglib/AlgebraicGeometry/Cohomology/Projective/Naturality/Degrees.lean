/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Naturality

/-!
# Original degree-equality maps in the projective Laurent comparison

Equality of twist degrees gives native equality morphisms of the actual sheaves and
of the sole Laurent complexes. Their unchanged homology/cohomology comparison retains
these original maps, in both directions.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory HomologicalComplex MvPolynomial
open AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Native degree equality on the original Laurent complex induces exactly the original
cohomology map of the native degree equality on the actual twist. -/
theorem twistingLaurentCohomologyLinearEquiv_eqToHom (a b : ℤ) (h : a = b) (q : ℕ)
    (x : (coordinateLaurentTupleComplex (ι := ι) R a).homology q) :
    twistingLaurentCohomologyLinearEquiv R ι b q
        (homologyMap (eqToHom (congrArg (coordinateLaurentTupleComplex (ι := ι) R) h)) q x) =
      Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
        (eqToHom (congrArg (twistingSheaf R ι) h))) q
          (twistingLaurentCohomologyLinearEquiv R ι a q x) := by
  subst b
  change twistingLaurentCohomologyLinearEquiv R ι a q
      (homologyMap (𝟙 (coordinateLaurentTupleComplex (ι := ι) R a)) q x) =
    Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
      (𝟙 (twistingSheaf R ι a))) q
      (twistingLaurentCohomologyLinearEquiv R ι a q x)
  rw [homologyMap_id]
  have hid := (SheafOfModules.toSheaf.{u} (ProjectiveSpace R ι).ringCatSheaf).map_id
    (twistingSheaf R ι a)
  rw [hid, Sheaf.H.map_id_apply]
  rfl

/-- The inverse original cohomology comparison retains the same native degree-equality map. -/
theorem twistingLaurentCohomologyLinearEquiv_symm_eqToHom (a b : ℤ) (h : a = b) (q : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) (twistingSheaf R ι a)) q) :
    (twistingLaurentCohomologyLinearEquiv R ι b q).symm
        (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
          (eqToHom (congrArg (twistingSheaf R ι) h))) q x) =
      homologyMap (eqToHom (congrArg (coordinateLaurentTupleComplex (ι := ι) R) h)) q
        ((twistingLaurentCohomologyLinearEquiv R ι a q).symm x) := by
  apply (twistingLaurentCohomologyLinearEquiv R ι b q).injective
  rw [LinearEquiv.apply_symm_apply,
    twistingLaurentCohomologyLinearEquiv_eqToHom R ι a b h q, LinearEquiv.apply_symm_apply]

end AlgebraicGeometry.Scheme.Cohomology
