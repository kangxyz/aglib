/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Generators
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Morphisms

/-!
# The actual tensor isomorphism of projective twists

The original pure tensors of standard generators glue to an inverse of the original
multiplication map. Both inverse equations are checked on original local sections, and
the forward map of the resulting native isomorphism is exactly that multiplication map.
No finiteness, Noetherianity or field hypothesis is required.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The original tensor generators satisfy the actual gluing equation for the sum twist. -/
theorem twistingTensorGenerator_compatible (a b : ℤ) (i j : ι)
    (V : (ProjectiveSpace R ι).Opens) (hi : V ≤ coordinateOpen R ι i)
    (hj : V ≤ coordinateOpen R ι j) :
    ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj
        (twistingSheaf R ι b)).val.map (homOfLE hj).op
        (twistingTensorGenerator R ι a b j le_rfl) =
      (((coordinateUnitCocycle R ι).zpow (-(a + b))).transitionOn i j hi hj).val •
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj
          (twistingSheaf R ι b)).val.map (homOfLE hi).op
          (twistingTensorGenerator R ι a b i le_rfl) := by
  rw [twistingTensorGenerator_restrict R ι a b j hj le_rfl,
    twistingTensorGenerator_restrict R ι a b i hi le_rfl,
    UnitCocycle.zpow_transitionOn, coordinateUnitCocycle_transitionOn]
  exact twistingTensorGenerator_transition R ι a b i j hi hj

/-- Gluing the original tensor generators constructs an actual inverse candidate to twist
multiplication, using the existing native internal-Hom sheaf gluing construction. -/
def twistingTensorInv (a b : ℤ) : twistingSheaf R ι (a + b) ⟶
    (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj
      (twistingSheaf R ι b) :=
  ((coordinateUnitCocycle R ι).zpow (-(a + b))).homOfLocalSections _
    (iSup_coordinateOpen_eq_top R ι) (fun i => twistingTensorGenerator R ι a b i le_rfl)
    (twistingTensorGenerator_compatible R ι a b)

/-- The inverse candidate is the original frame coefficient times the original tensor
of the standard generators on every coordinate subopen. -/
theorem twistingTensorInv_local (a b : ℤ) (i : ι)
    (V : (ProjectiveSpace R ι).Opens) (hi : V ≤ coordinateOpen R ι i)
    (s : Γ(twistingSheaf R ι (a + b), V)) :
    (twistingTensorInv R ι a b).val.app (op V) s =
      twistingSectionsEquiv R ι (a + b) i hi s • twistingTensorGenerator R ι a b i hi := by
  have h := ((coordinateUnitCocycle R ι).zpow (-(a + b))).homOfLocalSections_apply
    ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj
      (twistingSheaf R ι b))
    (iSup_coordinateOpen_eq_top R ι) (fun j => twistingTensorGenerator R ι a b j le_rfl)
    (twistingTensorGenerator_compatible R ι a b) i V hi s
  change (twistingTensorInv R ι a b).val.app (op V) s =
    twistingSectionsEquiv R ι (a + b) i hi s •
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj
        (twistingSheaf R ι b)).val.map (homOfLE hi).op
        (twistingTensorGenerator R ι a b i le_rfl) at h
  rw [twistingTensorGenerator_restrict R ι a b i hi le_rfl] at h
  exact h

/-- Glued inverse followed by original multiplication is the identity. -/
theorem twistingTensorInv_map (a b : ℤ) :
    twistingTensorInv R ι a b ≫ twistingTensorMap R ι a b =
      𝟙 (twistingSheaf R ι (a + b)) := by
  apply hom_ext_of_coordinateSubopens R ι
  intro i V hi s
  change (twistingTensorMap R ι a b).val.app (op V)
    ((twistingTensorInv R ι a b).val.app (op V) s) = s
  rw [twistingTensorInv_local R ι a b i V hi]
  rw [((twistingTensorMap R ι a b).val.app (op V)).hom.map_smul]
  rw [twistingTensorMap_generator, twistingSectionsEquiv_smul_generator]

/-- Original multiplication followed by its glued inverse fixes each original pure tensor
on every coordinate subopen. -/
theorem twistingTensorMap_inv_local (a b : ℤ) (i : ι)
    (V : (ProjectiveSpace R ι).Opens) (hi : V ≤ coordinateOpen R ι i)
    (s : Γ(twistingSheaf R ι a, V)) (t : Γ(twistingSheaf R ι b, V)) :
    (twistingTensorInv R ι a b).val.app (op V)
      ((twistingTensorMap R ι a b).val.app (op V)
        (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι a)
          (twistingSheaf R ι b) V s t)) =
      moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι a)
        (twistingSheaf R ι b) V s t := by
  rw [twistingTensorMap_section, twistingTensorInv_local R ι a b i V hi,
    twistingSectionsEquiv_mul, twistingTensorGenerator,
    ← twistingTensorSection_smul_smul, twistingSectionsEquiv_smul_generator,
    twistingSectionsEquiv_smul_generator]

/-- Original pure tensors and sheaf separation prove the other inverse equation globally. -/
theorem twistingTensorMap_inv (a b : ℤ) :
    twistingTensorMap R ι a b ≫ twistingTensorInv R ι a b =
      𝟙 ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj
        (twistingSheaf R ι b)) := by
  apply moduleTensor_hom_ext
  intro V s t
  let T := (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj
    (twistingSheaf R ι b)
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨T.presheaf, T.isSheaf⟩
    (fun i => V ⊓ coordinateOpen R ι i) V (fun _ => homOfLE inf_le_left)
    (by rw [← inf_iSup_eq, iSup_coordinateOpen_eq_top, inf_top_eq])
  intro i
  change T.val.map (homOfLE inf_le_left).op
      ((twistingTensorInv R ι a b).val.app (op V)
        ((twistingTensorMap R ι a b).val.app (op V)
          (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι a)
            (twistingSheaf R ι b) V s t))) =
    T.val.map (homOfLE inf_le_left).op
      (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι a)
        (twistingSheaf R ι b) V s t)
  rw [← PresheafOfModules.naturality_apply (twistingTensorInv R ι a b).val,
    ← PresheafOfModules.naturality_apply (twistingTensorMap R ι a b).val]
  change (twistingTensorInv R ι a b).val.app (op (V ⊓ coordinateOpen R ι i))
      ((twistingTensorMap R ι a b).val.app (op (V ⊓ coordinateOpen R ι i))
        (T.presheaf.map (homOfLE inf_le_left).op
          (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι a)
            (twistingSheaf R ι b) V s t))) =
    T.presheaf.map (homOfLE inf_le_left).op
      (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι a)
        (twistingSheaf R ι b) V s t)
  rw [moduleTensorSection_restrict]
  exact twistingTensorMap_inv_local R ι a b i _ inf_le_right _ _

/-- The native tensor product of the actual integer twists is the sum twist, with original
multiplication as its forward map and the original locally constructed inverse. -/
def twistingTensorIso (a b : ℤ) :
    (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj
        (twistingSheaf R ι b) ≅ twistingSheaf R ι (a + b) where
  hom := twistingTensorMap R ι a b
  inv := twistingTensorInv R ι a b
  hom_inv_id := twistingTensorMap_inv R ι a b
  inv_hom_id := twistingTensorInv_map R ι a b

/-- The native isomorphism retains the original twist multiplication morphism exactly. -/
theorem twistingTensorIso_hom (a b : ℤ) :
    (twistingTensorIso R ι a b).hom = twistingTensorMap R ι a b := rfl

end AlgebraicGeometry.ProjectiveSpace
