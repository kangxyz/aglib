/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting

/-!
# Original standard generators of projective twists

The standard generator on each coordinate subopen is the inverse image of one under the
original frame equivalence. Its restriction, coefficient reconstruction and transition
formulas retain the original sheaf maps and coordinate units.
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

/-- The original standard frame equivalence commutes with restriction to a smaller subopen. -/
theorem twistingSectionsEquiv_restrict (d : ℤ) (i : ι)
    {V W : (ProjectiveSpace R ι).Opens} (h : V ≤ W) (hi : W ≤ coordinateOpen R ι i)
    (s : Γ(twistingSheaf R ι d, W)) :
    twistingSectionsEquiv R ι d i (h.trans hi)
        ((twistingSheaf R ι d).val.map (homOfLE h).op s) =
      sectionRestrict (ProjectiveSpace R ι) h (twistingSectionsEquiv R ι d i hi s) :=
  ((coordinateUnitCocycle R ι).zpow (-d)).localSectionsEquiv_restrict i h hi s

/-- The original standard generator on a displayed coordinate subopen. -/
def twistingGenerator (d : ℤ) (i : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) : Γ(twistingSheaf R ι d, V) :=
  (twistingSectionsEquiv R ι d i hi).symm 1

/-- The original generator has coefficient exactly one. -/
@[simp]
theorem twistingSectionsEquiv_generator (d : ℤ) (i : ι)
    {V : (ProjectiveSpace R ι).Opens} (hi : V ≤ coordinateOpen R ι i) :
    twistingSectionsEquiv R ι d i hi (twistingGenerator R ι d i hi) = 1 :=
  (twistingSectionsEquiv R ι d i hi).apply_symm_apply 1

/-- Restricting an original generator gives the same original generator on the smaller open. -/
theorem twistingGenerator_restrict (d : ℤ) (i : ι)
    {V W : (ProjectiveSpace R ι).Opens} (h : V ≤ W) (hi : W ≤ coordinateOpen R ι i) :
    (twistingSheaf R ι d).val.map (homOfLE h).op (twistingGenerator R ι d i hi) =
      twistingGenerator R ι d i (h.trans hi) := by
  apply (twistingSectionsEquiv R ι d i (h.trans hi)).injective
  rw [twistingSectionsEquiv_restrict R ι d i h hi, twistingSectionsEquiv_generator,
    twistingSectionsEquiv_generator, map_one]

/-- Every original section is its frame coefficient times the original generator. -/
theorem twistingSectionsEquiv_smul_generator (d : ℤ) (i : ι)
    {V : (ProjectiveSpace R ι).Opens} (hi : V ≤ coordinateOpen R ι i)
    (s : Γ(twistingSheaf R ι d, V)) :
    twistingSectionsEquiv R ι d i hi s • twistingGenerator R ι d i hi = s := by
  apply (twistingSectionsEquiv R ι d i hi).injective
  rw [map_smul, twistingSectionsEquiv_generator, smul_eq_mul, mul_one]

/-- The original generators satisfy the inverse of the original coefficient transition rule. -/
theorem twistingGenerator_transition (d : ℤ) (i j : ι)
    {V : (ProjectiveSpace R ι).Opens} (hi : V ≤ coordinateOpen R ι i)
    (hj : V ≤ coordinateOpen R ι j) :
    twistingGenerator R ι d j hj =
      ((coordinateTransitionOn R ι i j hi hj ^ (-d)).val : Γ(ProjectiveSpace R ι, V)) •
        twistingGenerator R ι d i hi := by
  apply (twistingSectionsEquiv R ι d i hi).injective
  rw [twistingSectionsEquiv_transition R ι d i j hi hj,
    map_smul, twistingSectionsEquiv_generator, twistingSectionsEquiv_generator,
    smul_eq_mul]

/-- Original morphisms are determined on all subopens of the standard coordinate charts. -/
theorem hom_ext_of_coordinateSubopens {M N : (ProjectiveSpace R ι).Modules}
    {f g : M ⟶ N}
    (h : ∀ (i : ι) (V : (ProjectiveSpace R ι).Opens) (_ : V ≤ coordinateOpen R ι i)
      (s : Γ(M, V)), f.val.app (op V) s = g.val.app (op V) s) : f = g := by
  ext V s
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun i => V ⊓ coordinateOpen R ι i) V (fun _ => homOfLE inf_le_left)
    (by rw [← inf_iSup_eq, iSup_coordinateOpen_eq_top, inf_top_eq])
  intro i
  change N.val.map (homOfLE inf_le_left).op (f.val.app (op V) s) =
    N.val.map (homOfLE inf_le_left).op (g.val.app (op V) s)
  rw [← PresheafOfModules.naturality_apply f.val,
    ← PresheafOfModules.naturality_apply g.val]
  exact h i (V ⊓ coordinateOpen R ι i) inf_le_right _

end AlgebraicGeometry.ProjectiveSpace
