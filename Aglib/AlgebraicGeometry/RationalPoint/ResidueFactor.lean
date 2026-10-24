/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalPoint.Basic

/-! # The original residue-field factorization of a rational section

The existing section-induced residue equivalence gives an actual isomorphism
of field spectra. Its composite with the original residue-field point is the
original rational section. No algebraic closure or closedness premise is used.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RationalPoint

variable {k : Type u} [Field k] {X : Scheme.{u}} (q : RationalPoint k X)

/-- The existing residue equivalence is the original residue-field descent of
the section's actual stalk evaluation map. -/
theorem residueEquiv_hom_eq_descResidueField :
    q.residueEquiv.toCommRingCatIso.hom =
      X.descResidueField (Scheme.stalkClosedPointTo q.sectionMap) := by
  apply (cancel_epi (X.residue q.point)).mp
  rw [Scheme.residue_descResidueField]
  ext r
  exact q.residueEquiv_residue r

/-- The actual field-scheme isomorphism induced by the rational section's
original residue equivalence, oriented from the base field to the residue field. -/
def residueSpecIso : Spec (.of k) ≅ Spec (X.residueField q.point) :=
  Scheme.Spec.mapIso q.residueEquiv.toCommRingCatIso.op

/-- The actual residue-field factorization recovers the original section map. -/
@[reassoc (attr := simp)]
theorem residueSpecIso_hom_fromSpecResidueField :
    q.residueSpecIso.hom ≫ X.fromSpecResidueField q.point = q.sectionMap := by
  change Spec.map q.residueEquiv.toCommRingCatIso.hom ≫
    X.fromSpecResidueField q.point = q.sectionMap
  rw [residueEquiv_hom_eq_descResidueField]
  exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k X q.sectionMap

/-- The residue point's original structure map is the inverse of the actual
rational residue-field isomorphism. -/
theorem fromSpecResidueField_structureMap :
    X.fromSpecResidueField q.point ≫ q.structureMap = q.residueSpecIso.inv := by
  apply (cancel_epi q.residueSpecIso.hom).mp
  rw [residueSpecIso_hom_fromSpecResidueField_assoc, q.section_comp, Iso.hom_inv_id]

end AlgebraicGeometry.Scheme.RationalPoint
