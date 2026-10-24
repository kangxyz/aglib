/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.FieldConservative
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ConnectedTorsionSections

/-! # Actual constant counits over separably closed fields

For an actual abelian sheaf whose original global section group is torsion,
the original constant-adjunction counit is an isomorphism. The proof uses the
actual constant unit, adjunction triangle and conservative original global
sections. This is a sheaf identification, not a new cohomology model or PBC.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- The actual constant-adjunction counit is invertible when the original
section group is torsion. No finite coefficient cardinality is required. -/
theorem constantCounit_isIso_of_field_torsionSections
    (F : AbelianSheaf.{u, u + 1} (Spec (.of Ω)))
    (hF : IsAddTorsion ((globalSections (Spec (.of Ω))).obj F)) :
    IsIso ((constantAdjunction (Spec (.of Ω))).counit.app F) := by
  let a := constantAdjunction (Spec (.of Ω))
  let : IsIso (a.unit.app ((globalSections (Spec (.of Ω))).obj F)) :=
    constantUnit_isIso_of_isAddTorsion (Spec (.of Ω)) _ hF
  have : IsIso ((globalSections (Spec (.of Ω))).map (a.counit.app F)) := by
    apply (isIso_comp_left_iff (a.unit.app ((globalSections (Spec (.of Ω))).obj F)) _).mp
    rw [a.right_triangle_components]
    exact (Iso.refl ((globalSections (Spec (.of Ω))).obj F)).isIso_hom
  exact isIso_of_field_globalSections Ω (a.counit.app F)

/-- The original sheaf is constant with its original global sections; the
inverse arrow is exactly the native adjunction counit. -/
def fieldTorsionConstantIso
    (F : AbelianSheaf.{u, u + 1} (Spec (.of Ω)))
    (hF : IsAddTorsion ((globalSections (Spec (.of Ω))).obj F)) :
    F ≅ (constantSheaf (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      ((globalSections (Spec (.of Ω))).obj F) := by
  let := constantCounit_isIso_of_field_torsionSections Ω F hF
  exact (asIso ((constantAdjunction (Spec (.of Ω))).counit.app F)).symm

/-- The actual counit is retained, rather than replacing the constant model
by an unnormalized chosen equivalence. -/
theorem fieldTorsionConstantIso_inv
    (F : AbelianSheaf.{u, u + 1} (Spec (.of Ω)))
    (hF : IsAddTorsion ((globalSections (Spec (.of Ω))).obj F)) :
    (fieldTorsionConstantIso Ω F hF).inv =
      (constantAdjunction (Spec (.of Ω))).counit.app F := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
