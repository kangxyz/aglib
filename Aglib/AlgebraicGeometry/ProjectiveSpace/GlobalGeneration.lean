/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.HomogeneousSections
public import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Global generation of nonnegative projective twists

The actual global sections `Xᵢ^n` define an epimorphism from the free module sheaf on the
coordinate type to the actual `O(n)`, for every `n ≥ 0`. On the `i` chart the corresponding
section is `1` in the canonical frame, which proves local surjectivity of the original map.
The generating family is finite whenever the coordinate type is finite.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MvPolynomial TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The compatible section family underlying an actual homogeneous-polynomial global section. -/
def homogeneousSectionFamily (n : ℕ) (p : homogeneousSubmodule ι R n) :
    (twistingSheaf R ι (n : ℤ)).sections :=
  _root_.PresheafOfModules.sectionsMk
    (fun V => (twistingSheaf R ι (n : ℤ)).val.map (homOfLE le_top).op
      (homogeneousSection R ι n p)) (by
        intro V W f
        rw [← _root_.PresheafOfModules.map_comp_apply]
        rfl)

/-- The coordinate-power section has coefficient `1` on every subopen of its own chart. -/
theorem homogeneousSectionFamily_coordinatePower_local (n : ℕ) (i : ι)
    {V : (ProjectiveSpace R ι).Opens} (hi : V ≤ coordinateOpen R ι i) :
    twistingSectionsEquiv R ι (n : ℤ) i hi
      ((homogeneousSectionFamily R ι n (coordinatePower R ι n i)).val (op V)) = 1 := by
  change sectionRestrict (ProjectiveSpace R ι) (le_inf le_rfl hi)
    (sectionRestrict (ProjectiveSpace R ι) (inf_le_inf le_top le_rfl)
      (sectionRestrict (ProjectiveSpace R ι) inf_le_right
        (homogeneousChartSection R ι n (coordinatePower R ι n i) i))) = 1
  rw [sectionRestrict_comp, sectionRestrict_comp]
  simp [homogeneousChartSection]

/-- The actual map from the free structure-module sheaf defined by the sections `Xᵢ^n`. -/
def coordinatePowerGeneratingMap (n : ℕ) :
    SheafOfModules.free (R := (ProjectiveSpace R ι).ringCatSheaf) ι ⟶
      twistingSheaf R ι (n : ℤ) :=
  (twistingSheaf R ι (n : ℤ)).freeHomEquiv.symm
    (fun i => homogeneousSectionFamily R ι n (coordinatePower R ι n i))

/-- The generating map sends each original free section to its specified coordinate power. -/
theorem coordinatePowerGeneratingMap_freeSection (n : ℕ) (i : ι)
    (V : (ProjectiveSpace R ι).Opens) :
    (coordinatePowerGeneratingMap R ι n).val.app (op V)
        ((SheafOfModules.freeSection (R := (ProjectiveSpace R ι).ringCatSheaf) i).val (op V)) =
      (homogeneousSectionFamily R ι n (coordinatePower R ι n i)).val (op V) :=
  congrArg (fun s : (twistingSheaf R ι (n : ℤ)).sections => s.val (op V))
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (fun j => homogeneousSectionFamily R ι n (coordinatePower R ι n j)) i)

/-- Coordinate powers globally generate the actual nonnegative twisting sheaf. -/
instance coordinatePowerGeneratingMap_epi (n : ℕ) : Epi (coordinatePowerGeneratingMap R ι n) := by
  let : (SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).ReflectsEpimorphisms :=
    Functor.reflectsEpimorphisms_of_faithful _
  apply (SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).epi_of_epi_map
  suffices h : Sheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
        (coordinatePowerGeneratingMap R ι n)) by
    let := h
    infer_instance
  apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
  intro V s x hxV
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ iSup (coordinateOpen R ι) by
    rw [iSup_coordinateOpen_eq_top]; trivial)
  let W := V ⊓ coordinateOpen R ι i
  let sW : (twistingSheaf R ι (n : ℤ)).val.obj (op W) :=
    (twistingSheaf R ι (n : ℤ)).val.map (homOfLE inf_le_left).op s
  let a : Γ(ProjectiveSpace R ι, W) := twistingSectionsEquiv R ι (n : ℤ) i inf_le_right sW
  let basis : (SheafOfModules.free (R := (ProjectiveSpace R ι).ringCatSheaf) ι).val.obj (op W) :=
    (SheafOfModules.freeSection (R := (ProjectiveSpace R ι).ringCatSheaf) i).val (op W)
  refine ⟨W, inf_le_left, ?_, hxV, hi⟩
  refine ⟨a • basis, ?_⟩
  change (coordinatePowerGeneratingMap R ι n).val.app (op W) (a • basis) = sW
  rw [map_smul, coordinatePowerGeneratingMap_freeSection]
  apply (twistingSectionsEquiv R ι (n : ℤ) i inf_le_right).injective
  rw [map_smul, homogeneousSectionFamily_coordinatePower_local, smul_eq_mul, mul_one]

/-- The actual globally generating coordinate-power section family. -/
def coordinatePowerGeneratingSections (n : ℕ) :
    (twistingSheaf R ι (n : ℤ)).GeneratingSections where
  I := ι
  s i := homogeneousSectionFamily R ι n (coordinatePower R ι n i)
  epi := coordinatePowerGeneratingMap_epi R ι n

instance coordinatePowerGeneratingSections_isFiniteType [Finite ι] (n : ℕ) :
    (coordinatePowerGeneratingSections R ι n).IsFiniteType where
  finite := inferInstanceAs (Finite ι)

end AlgebraicGeometry.ProjectiveSpace
