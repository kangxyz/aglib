/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Hom.Coefficients

/-!
# Actual morphisms between twists and original global sections

The original local frame coefficients of a morphism `O(b) → O(a+b)` form a global
section of `O(a)`. Its inverse is the original section multiplication morphism.
Both equations retain the original sheaf restrictions and standard generators.
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

/-- Original frame coefficients form the actual matching-family global section. -/
def twistingHomSection (a b : ℤ)
    (f : twistingSheaf R ι b ⟶ twistingSheaf R ι (a + b)) :
    Γ(twistingSheaf R ι a, ⊤) := by
  change ((coordinateUnitCocycle R ι).zpow (-a)).Sections ⊤
  refine ⟨fun i => twistingHomCoefficient R ι a b f i
    (V := ⊤ ⊓ coordinateOpen R ι i) inf_le_right, ?_⟩
  intro V hV i j hi hj
  change sectionRestrict (ProjectiveSpace R ι) (le_inf hV hi)
      (twistingHomCoefficient R ι a b f i inf_le_right) =
    (((coordinateUnitCocycle R ι).zpow (-a)).transitionOn i j hi hj).val *
      sectionRestrict (ProjectiveSpace R ι) (le_inf hV hj)
        (twistingHomCoefficient R ι a b f j inf_le_right)
  rw [twistingHomCoefficient_restrict R ι a b f i (le_inf hV hi) inf_le_right,
    twistingHomCoefficient_restrict R ι a b f j (le_inf hV hj) inf_le_right,
    UnitCocycle.zpow_transitionOn, coordinateUnitCocycle_transitionOn]
  exact twistingHomCoefficient_transition R ι a b f i j hi hj

/-- The actual global section recovers the original coefficient on every coordinate subopen. -/
theorem twistingHomSection_local (a b : ℤ)
    (f : twistingSheaf R ι b ⟶ twistingSheaf R ι (a + b)) (i : ι)
    {V : (ProjectiveSpace R ι).Opens} (hi : V ≤ coordinateOpen R ι i) :
    twistingSectionsEquiv R ι a i hi
        ((twistingSheaf R ι a).val.map (homOfLE le_top).op (twistingHomSection R ι a b f)) =
      twistingHomCoefficient R ι a b f i hi := by
  change sectionRestrict (ProjectiveSpace R ι) (le_inf le_rfl hi)
      (sectionRestrict (ProjectiveSpace R ι) (inf_le_inf le_top le_rfl)
        (twistingHomCoefficient R ι a b f i
          (V := ⊤ ⊓ coordinateOpen R ι i) inf_le_right)) = _
  rw [sectionRestrict_comp]
  exact twistingHomCoefficient_restrict R ι a b f i (le_inf le_top hi) inf_le_right

/-- Multiplication by the recovered original section is the original actual morphism. -/
theorem twistingMultiplyGlobal_homSection (a b : ℤ)
    (f : twistingSheaf R ι b ⟶ twistingSheaf R ι (a + b)) :
    twistingMultiplyGlobal R ι a b (twistingHomSection R ι a b f) = f := by
  apply hom_ext_of_coordinateSubopens R ι
  intro i V hi s
  apply (twistingSectionsEquiv R ι (a + b) i hi).injective
  rw [twistingMultiplyGlobal_app, twistingSectionsEquiv_mul, twistingHomSection_local]
  calc
    twistingHomCoefficient R ι a b f i hi * twistingSectionsEquiv R ι b i hi s =
        twistingSectionsEquiv R ι b i hi s * twistingHomCoefficient R ι a b f i hi :=
      mul_comm _ _
    _ = twistingSectionsEquiv R ι (a + b) i hi
        (f.val.app (op V)
          (twistingSectionsEquiv R ι b i hi s • twistingGenerator R ι b i hi)) := by
      rw [(f.val.app (op V)).hom.map_smul,
        (twistingSectionsEquiv R ι (a + b) i hi).map_smul, smul_eq_mul]
      rfl
    _ = twistingSectionsEquiv R ι (a + b) i hi (f.val.app (op V) s) := by
      rw [twistingSectionsEquiv_smul_generator]

/-- Recovering the section of an original multiplication morphism gives the original section. -/
theorem twistingHomSection_multiplyGlobal (a b : ℤ) (s : Γ(twistingSheaf R ι a, ⊤)) :
    twistingHomSection R ι a b (twistingMultiplyGlobal R ι a b s) = s := by
  apply TopCat.Sheaf.eq_of_locally_eq'
    ⟨(twistingSheaf R ι a).presheaf, (twistingSheaf R ι a).isSheaf⟩
    (coordinateOpen R ι) ⊤ (fun _ => homOfLE le_top)
    (le_of_eq (iSup_coordinateOpen_eq_top R ι).symm)
  intro i
  change (twistingSheaf R ι a).val.map (homOfLE le_top).op
      (twistingHomSection R ι a b (twistingMultiplyGlobal R ι a b s)) =
    (twistingSheaf R ι a).val.map (homOfLE le_top).op s
  apply (twistingSectionsEquiv R ι a i le_rfl).injective
  rw [twistingHomSection_local, twistingHomCoefficient_multiplyGlobal]

/-- Original global sections of the difference twist identify additively with actual
morphisms between the twists. The forward map is original multiplication. -/
def twistingGlobalSectionsHomAddEquiv (a b : ℤ) :
    Γ(twistingSheaf R ι a, ⊤) ≃+
      (twistingSheaf R ι b ⟶ twistingSheaf R ι (a + b)) where
  toFun := twistingMultiplyGlobal R ι a b
  invFun := twistingHomSection R ι a b
  left_inv := twistingHomSection_multiplyGlobal R ι a b
  right_inv := twistingMultiplyGlobal_homSection R ι a b
  map_add' := twistingMultiplyGlobal_add R ι a b

/-- The additive Hom comparison retains exactly the original multiplication morphism. -/
theorem twistingGlobalSectionsHomAddEquiv_apply (a b : ℤ)
    (s : Γ(twistingSheaf R ι a, ⊤)) :
    twistingGlobalSectionsHomAddEquiv R ι a b s = twistingMultiplyGlobal R ι a b s := rfl

end AlgebraicGeometry.ProjectiveSpace
