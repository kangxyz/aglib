/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Transition
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing

/-!
# Actual twisting module sheaves on polynomial projective space

For every integer `n`, the standard transition units construct an actual locally rank-one module
sheaf `O(n)` on Mathlib's polynomial `Proj`. In the local frame `Xᵢ^n`, coefficient functions
satisfy `sᵢ = (Xᵢ / Xⱼ)^(-n) sⱼ`. The construction works over every commutative ring and with
every coordinate type. Finite presentation and quasicoherence follow from the same local bases.
Transport along an equality of degrees keeps chart functions (`twistingSection_eqToHom_val`) and
frame coefficients (`twistingSectionsEquiv_eqToHom`).
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MvPolynomial TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- A common subopen of two coordinate charts lies in the native product principal open. -/
theorem le_basicOpen_coordinate_mul (i j : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) (hj : V ≤ coordinateOpen R ι j) :
    V ≤ Proj.basicOpen (homogeneousSubmodule ι R) (X i * X j) := by
  rw [Proj.basicOpen_mul]
  exact le_inf hi hj

/-- The original coordinate transition unit restricted to any displayed common subopen. -/
def coordinateTransitionOn (i j : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) (hj : V ≤ coordinateOpen R ι j) :
    (Γ(ProjectiveSpace R ι, V))ˣ :=
  Units.map (sectionRestrict (ProjectiveSpace R ι)
    (le_basicOpen_coordinate_mul R ι i j hi hj)).toMonoidHom
      (coordinateTransitionSectionUnit R ι i j)

/-- Coordinate transition units commute with the actual restrictions to smaller common opens. -/
theorem coordinateTransitionOn_restrict (i j : ι) {V W : (ProjectiveSpace R ι).Opens}
    (h : V ≤ W) (hi : W ≤ coordinateOpen R ι i) (hj : W ≤ coordinateOpen R ι j) :
    Units.map (sectionRestrict (ProjectiveSpace R ι) h).toMonoidHom
        (coordinateTransitionOn R ι i j hi hj) =
      coordinateTransitionOn R ι i j (h.trans hi) (h.trans hj) := by
  apply Units.ext
  exact sectionRestrict_comp (ProjectiveSpace R ι) _ _ _

/-- The proved native overlap cocycle restricts to every common subopen of three charts. -/
theorem coordinateTransitionOn_cocycle (i j k : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) (hj : V ≤ coordinateOpen R ι j)
    (hk : V ≤ coordinateOpen R ι k) :
    coordinateTransitionOn R ι i j hi hj * coordinateTransitionOn R ι j k hj hk =
      coordinateTransitionOn R ι i k hi hk := by
  have hV : V ≤ Proj.basicOpen (homogeneousSubmodule ι R) (X i * X j * X k) := by
    rw [Proj.basicOpen_mul, Proj.basicOpen_mul]
    exact le_inf (le_inf hi hj) hk
  have h := congrArg (fun z :
      (Γ(ProjectiveSpace R ι,
        Proj.basicOpen (homogeneousSubmodule ι R) (X i * X j * X k)))ˣ =>
      sectionRestrict (ProjectiveSpace R ι) hV z.val)
    (coordinateTransitionSectionUnit_cocycle R ι i j k)
  apply Units.ext
  change sectionRestrict (ProjectiveSpace R ι)
        (le_basicOpen_coordinate_mul R ι i j hi hj)
        (coordinateTransitionSectionUnit R ι i j).val *
      sectionRestrict (ProjectiveSpace R ι)
        (le_basicOpen_coordinate_mul R ι j k hj hk)
        (coordinateTransitionSectionUnit R ι j k).val =
      sectionRestrict (ProjectiveSpace R ι)
        (le_basicOpen_coordinate_mul R ι i k hi hk)
        (coordinateTransitionSectionUnit R ι i k).val
  change sectionRestrict (ProjectiveSpace R ι) hV
      (coordinateOverlapSectionsToTriple₀₁ R ι i j k
          (coordinateTransitionSectionUnit R ι i j).val *
        coordinateOverlapSectionsToTriple₁₂ R ι i j k
          (coordinateTransitionSectionUnit R ι j k).val) =
      sectionRestrict (ProjectiveSpace R ι) hV
        (coordinateOverlapSectionsToTriple₀₂ R ι i j k
          (coordinateTransitionSectionUnit R ι i k).val) at h
  simpa only [coordinateOverlapSectionsToTriple₀₁, coordinateOverlapSectionsToTriple₁₂,
    coordinateOverlapSectionsToTriple₀₂, map_mul, sectionRestrict_comp] using h

/-- The actual projective coordinate units form gluing data on the standard open cover. -/
def coordinateUnitCocycle : UnitCocycle (coordinateOpen R ι) where
  transition i j := coordinateTransitionOn R ι i j inf_le_left inf_le_right
  cocycle i j k V hi hj hk := by
    rw [coordinateTransitionOn_restrict, coordinateTransitionOn_restrict,
      coordinateTransitionOn_restrict]
    exact coordinateTransitionOn_cocycle R ι i j k hi hj hk

@[simp]
theorem coordinateUnitCocycle_transitionOn (i j : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) (hj : V ≤ coordinateOpen R ι j) :
    (coordinateUnitCocycle R ι).transitionOn i j hi hj =
      coordinateTransitionOn R ι i j hi hj :=
  coordinateTransitionOn_restrict R ι i j (le_inf hi hj) inf_le_left inf_le_right

/-- The actual twisting module sheaf `O(n)` on polynomial projective space. -/
def twistingSheaf (n : ℤ) : (ProjectiveSpace R ι).Modules :=
  ((coordinateUnitCocycle R ι).zpow (-n)).sheaf

/-- The same standard-coordinate singleton bases prove finite local freeness of every twist. -/
instance twistingSheaf_isFiniteLocallyFree (n : ℤ) :
    Scheme.Modules.IsFiniteLocallyFree (ProjectiveSpace R ι) (twistingSheaf R ι n) :=
  ((coordinateUnitCocycle R ι).zpow (-n)).isFiniteLocallyFree (iSup_coordinateOpen_eq_top R ι)

/-- Twisting sheaves are locally of rank one. -/
theorem isLocallyRankOne_twistingSheaf (d : ℤ) :
    IsLocallyRankOne (ProjectiveSpace R ι) (twistingSheaf R ι d) :=
  ((coordinateUnitCocycle R ι).zpow (-d)).isLocallyRankOne (iSup_coordinateOpen_eq_top R ι)

/-- The twisting sheaf as an actual line bundle, with its chosen standard-cover rank-one proof. -/
def twistingLineBundle (n : ℤ) : LineBundle (ProjectiveSpace R ι) :=
  ((coordinateUnitCocycle R ι).zpow (-n)).lineBundle (iSup_coordinateOpen_eq_top R ι)

/-- Projection to the coefficient in the frame `Xᵢ^n` trivializes the actual twisting sheaf. -/
def twistingLocalIso (n : ℤ) (i : ι) :
    (twistingSheaf R ι n).over (coordinateOpen R ι i) ≅
      SheafOfModules.unit ((ProjectiveSpace R ι).ringCatSheaf.over (coordinateOpen R ι i)) :=
  ((coordinateUnitCocycle R ι).zpow (-n)).localIso i

/-- Sections of `O(n)` on every subopen of the `i` chart are its ordinary functions, in the
specified local frame and with the original section-ring action. -/
def twistingSectionsEquiv (n : ℤ) (i : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) :
    ((twistingSheaf R ι n).val.obj (Opposite.op V)) ≃ₗ[Γ(ProjectiveSpace R ι, V)]
      Γ(ProjectiveSpace R ι, V) :=
  ((coordinateUnitCocycle R ι).zpow (-n)).localSectionsEquiv i hi

/-- The actual frame coordinates satisfy the standard `O(n)` transition rule. -/
theorem twistingSectionsEquiv_transition (n : ℤ) (i j : ι)
    {V : (ProjectiveSpace R ι).Opens} (hi : V ≤ coordinateOpen R ι i)
    (hj : V ≤ coordinateOpen R ι j) (s : (twistingSheaf R ι n).val.obj (Opposite.op V)) :
    twistingSectionsEquiv R ι n i hi s =
      ((coordinateTransitionOn R ι i j hi hj ^ (-n) :
        (Γ(ProjectiveSpace R ι, V))ˣ) : Γ(ProjectiveSpace R ι, V)) *
          twistingSectionsEquiv R ι n j hj s := by
  exact (((coordinateUnitCocycle R ι).zpow (-n)).localSectionsEquiv_transition i j hi hj s).trans
    (by rw [UnitCocycle.zpow_transitionOn, coordinateUnitCocycle_transitionOn]; rfl)

/-- Transport along an equality of twist degrees keeps every matching chart function. -/
theorem twistingSection_eqToHom_val {c c' : ℤ} (h : c = c') {U : (ProjectiveSpace R ι).Opens}
    (x : Γ(twistingSheaf R ι c, U)) (i : ι) :
    ((eqToHom (congrArg (twistingSheaf R ι) h)).val.app (Opposite.op U) x).val i = x.val i := by
  subst h
  rfl

/-- Transport along an equality of degrees keeps the standard frame coefficient. -/
theorem twistingSectionsEquiv_eqToHom {c c' : ℤ} (h : c = c') (i : ι)
    {V : (ProjectiveSpace R ι).Opens} (hV : V ≤ coordinateOpen R ι i)
    (x : (twistingSheaf R ι c).val.obj (Opposite.op V)) :
    twistingSectionsEquiv R ι c' i hV
        ((eqToHom (congrArg (twistingSheaf R ι) h)).val.app (Opposite.op V) x) =
      twistingSectionsEquiv R ι c i hV x := by
  subst h
  rfl

end AlgebraicGeometry.ProjectiveSpace
