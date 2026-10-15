/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Hom.Sections
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Morphisms

/-!
# The actual zero twist and structure module

The constant local coefficient one glues the canonical morphism from the original zero
twist to the structure module. Its inverse is the original section associated to the
identity of the zero twist. Both maps retain the standard local frame coefficients.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The original section with coefficient one in every standard frame of the zero twist. -/
def twistingUnitSection : Γ(twistingSheaf R ι 0, ⊤) :=
  twistingHomSection R ι 0 0 (𝟙 _)

/-- The original unit section has exactly coefficient one on every coordinate subopen. -/
theorem twistingUnitSection_local (i : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) :
    twistingSectionsEquiv R ι 0 i hi
        ((twistingSheaf R ι 0).val.map (homOfLE le_top).op (twistingUnitSection R ι)) = 1 := by
  rw [twistingUnitSection, twistingHomSection_local]
  change twistingSectionsEquiv R ι 0 i hi (twistingGenerator R ι 0 i hi) = 1
  exact twistingSectionsEquiv_generator R ι 0 i hi

/-- The original unit sections satisfy the original zero-twist cocycle equation. -/
theorem twistingZero_unit_compatible (i j : ι) (V : (ProjectiveSpace R ι).Opens)
    (hi : V ≤ coordinateOpen R ι i) (hj : V ≤ coordinateOpen R ι j) :
    (SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf).val.map
        (homOfLE hj).op (1 : Γ(ProjectiveSpace R ι, coordinateOpen R ι j)) =
      (((coordinateUnitCocycle R ι).zpow (-(0 : ℤ))).transitionOn i j hi hj).val •
        (SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf).val.map
          (homOfLE hi).op (1 : Γ(ProjectiveSpace R ι, coordinateOpen R ι i)) := by
  rw [UnitCocycle.zpow_transitionOn]
  change sectionRestrict (ProjectiveSpace R ι) hj 1 =
    (((coordinateUnitCocycle R ι).transitionOn i j hi hj) ^ (-(0 : ℤ))).val *
      sectionRestrict (ProjectiveSpace R ι) hi 1
  simp

/-- The actual zero twist maps to the structure module by its original frame coefficient. -/
def twistingZeroToUnit : twistingSheaf R ι 0 ⟶
    SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf :=
  ((coordinateUnitCocycle R ι).zpow (-(0 : ℤ))).homOfLocalSections _
    (iSup_coordinateOpen_eq_top R ι)
    (fun i => (1 : Γ(ProjectiveSpace R ι, coordinateOpen R ι i)))
    (twistingZero_unit_compatible R ι)

/-- The original glued map is exactly the standard frame coefficient. -/
theorem twistingZeroToUnit_app (i : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) (s : Γ(twistingSheaf R ι 0, V)) :
    (twistingZeroToUnit R ι).val.app (op V) s = twistingSectionsEquiv R ι 0 i hi s := by
  have h := ((coordinateUnitCocycle R ι).zpow (-(0 : ℤ))).homOfLocalSections_apply
    (SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf)
    (iSup_coordinateOpen_eq_top R ι)
    (fun j => (1 : Γ(ProjectiveSpace R ι, coordinateOpen R ι j)))
    (twistingZero_unit_compatible R ι) i V hi s
  change (twistingZeroToUnit R ι).val.app (op V) s =
    twistingSectionsEquiv R ι 0 i hi s * sectionRestrict (ProjectiveSpace R ι) hi 1 at h
  simpa only [map_one, mul_one] using h

/-- The original global unit section defines the inverse morphism from the structure module. -/
def unitToTwistingZero : SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf ⟶
    twistingSheaf R ι 0 :=
  (Scheme.Modules.unitHomGlobalSectionsEquiv (ProjectiveSpace R ι)
    (twistingSheaf R ι 0)).symm (twistingUnitSection R ι)

/-- The inverse original morphism has exactly the input function as its frame coefficient. -/
theorem unitToTwistingZero_app (i : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) (r : Γ(ProjectiveSpace R ι, V)) :
    twistingSectionsEquiv R ι 0 i hi ((unitToTwistingZero R ι).val.app (op V) r) = r := by
  change twistingSectionsEquiv R ι 0 i hi
    (Scheme.Modules.Hom.app ((Scheme.Modules.unitHomGlobalSectionsEquiv
      (ProjectiveSpace R ι) (twistingSheaf R ι 0)).symm (twistingUnitSection R ι)) V r) = r
  rw [Scheme.Modules.unitHomGlobalSectionsEquiv_symm_app]
  rw [(twistingSectionsEquiv R ι 0 i hi).map_smul]
  change r * twistingSectionsEquiv R ι 0 i hi
    ((twistingSheaf R ι 0).val.map (homOfLE le_top).op (twistingUnitSection R ι)) = r
  rw [twistingUnitSection_local, mul_one]

/-- The actual zero twist is the actual structure module, with the original local frames. -/
def twistingZeroIso : twistingSheaf R ι 0 ≅
    SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf where
  hom := twistingZeroToUnit R ι
  inv := unitToTwistingZero R ι
  hom_inv_id := by
    apply hom_ext_of_coordinateSubopens R ι
    intro i V hi s
    apply (twistingSectionsEquiv R ι 0 i hi).injective
    change twistingSectionsEquiv R ι 0 i hi
      ((unitToTwistingZero R ι).val.app (op V) ((twistingZeroToUnit R ι).val.app (op V) s)) = _
    rw [unitToTwistingZero_app R ι i hi, twistingZeroToUnit_app R ι i hi]
    rfl
  inv_hom_id := by
    apply hom_ext_of_coordinateSubopens R ι
    intro i V hi r
    change (twistingZeroToUnit R ι).val.app (op V)
      ((unitToTwistingZero R ι).val.app (op V) r) = r
    rw [twistingZeroToUnit_app R ι i hi, unitToTwistingZero_app R ι i hi]

end AlgebraicGeometry.ProjectiveSpace
