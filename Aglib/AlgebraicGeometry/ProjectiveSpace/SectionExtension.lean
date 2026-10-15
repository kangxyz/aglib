/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.PrincipalOpen
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineOpenSections

/-!
# Extending actual projective module sections by coordinate powers

Native affine localization clears denominators of quasicoherent module sections on each
standard chart. A finite coordinate cover gives a common power for all local numerators.
The original ratio functions and transition units are retained for the subsequent overlap
torsion and gluing argument.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineOpenSections

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)
  (M : (ProjectiveSpace R ι).Modules) [M.IsQuasicoherent]

/-- A section on a two-chart overlap has a numerator on the first chart after multiplication
by a power of the original coordinate ratio. -/
theorem coordinateSection_exists_power_extend (j i : ι)
    (s : Γ(M, coordinateOpen R ι j ⊓ coordinateOpen R ι i)) :
    ∃ (n : ℕ) (t : Γ(M, coordinateOpen R ι j)),
      M.presheaf.map (homOfLE (inf_le_left :
        coordinateOpen R ι j ⊓ coordinateOpen R ι i ≤ coordinateOpen R ι j)).op t =
        ((ProjectiveSpace R ι).presheaf.map (homOfLE (inf_le_left :
          coordinateOpen R ι j ⊓ coordinateOpen R ι i ≤ coordinateOpen R ι j)).op
          (coordinateRatioSection R ι j i)) ^ n • s := by
  have haux (W : (ProjectiveSpace R ι).Opens)
      (hW : (ProjectiveSpace R ι).basicOpen (coordinateRatioSection R ι j i) = W)
      (hWj : W ≤ coordinateOpen R ι j) (s : Γ(M, W)) :
      ∃ (n : ℕ) (t : Γ(M, coordinateOpen R ι j)),
        M.presheaf.map (homOfLE hWj).op t =
          ((ProjectiveSpace R ι).presheaf.map (homOfLE hWj).op
            (coordinateRatioSection R ι j i)) ^ n • s := by
    subst W
    exact exists_power_mul_eq_restriction M (isAffineOpen_coordinateOpen R ι j)
      (coordinateRatioSection R ι j i) s
  exact haux _ (basicOpen_coordinateRatioSection R ι j i) inf_le_left s

/-- Vanishing on a two-chart overlap is annihilated by a power of the original ratio. -/
theorem coordinateSection_exists_power_annihilate (j i : ι)
    (t : Γ(M, coordinateOpen R ι j))
    (ht : M.presheaf.map
      (homOfLE (inf_le_left : coordinateOpen R ι j ⊓ coordinateOpen R ι i ≤
        coordinateOpen R ι j)).op t = 0) :
    ∃ n : ℕ, coordinateRatioSection R ι j i ^ n • t = 0 := by
  have haux (W : (ProjectiveSpace R ι).Opens)
      (hW : (ProjectiveSpace R ι).basicOpen (coordinateRatioSection R ι j i) = W)
      (hWj : W ≤ coordinateOpen R ι j) :
      M.presheaf.map (homOfLE hWj).op t = 0 →
        ∃ n : ℕ, coordinateRatioSection R ι j i ^ n • t = 0 := by
    subst W
    exact exists_power_smul_eq_zero M (isAffineOpen_coordinateOpen R ι j)
      (coordinateRatioSection R ι j i) t
  exact haux _ (basicOpen_coordinateRatioSection R ι j i) inf_le_left ht

/-- A finite coordinate cover supplies one common denominator exponent and actual numerator
sections on all charts for a section on the distinguished chart. -/
theorem exists_coordinateChartNumerators [Finite ι] (i : ι)
    (s : Γ(M, coordinateOpen R ι i)) :
    ∃ (N : ℕ) (t : ∀ j, Γ(M, coordinateOpen R ι j)), ∀ j,
      M.presheaf.map (homOfLE (inf_le_left :
        coordinateOpen R ι j ⊓ coordinateOpen R ι i ≤ coordinateOpen R ι j)).op (t j) =
        ((ProjectiveSpace R ι).presheaf.map (homOfLE (inf_le_left :
          coordinateOpen R ι j ⊓ coordinateOpen R ι i ≤ coordinateOpen R ι j)).op
          (coordinateRatioSection R ι j i)) ^ N •
            M.presheaf.map (homOfLE (inf_le_right :
              coordinateOpen R ι j ⊓ coordinateOpen R ι i ≤ coordinateOpen R ι i)).op s := by
  classical
  let := Fintype.ofFinite ι
  choose n t ht using fun j => coordinateSection_exists_power_extend R ι M j i
    (M.presheaf.map (homOfLE (inf_le_right :
      coordinateOpen R ι j ⊓ coordinateOpen R ι i ≤ coordinateOpen R ι i)).op s)
  let N := Finset.univ.sup n
  refine ⟨N, fun j => coordinateRatioSection R ι j i ^ (N - n j) • t j, ?_⟩
  intro j
  have hn : n j ≤ N := Finset.le_sup (Finset.mem_univ j)
  rw [Scheme.Modules.map_smul, map_pow, ht]
  rw [← mul_smul, ← pow_add, Nat.sub_add_cancel hn]

variable {M}

/-- On every common subopen, coordinate ratios retain the original projective transition
equation used to compare local numerator sections. -/
theorem coordinateRatioSection_transition (i j k : ι) {V : (ProjectiveSpace R ι).Opens}
    (hj : V ≤ coordinateOpen R ι j) (hk : V ≤ coordinateOpen R ι k) :
    sectionRestrict (ProjectiveSpace R ι) hj (coordinateRatioSection R ι j i) =
      ((coordinateTransitionOn R ι j k hj hk)⁻¹).val *
        sectionRestrict (ProjectiveSpace R ι) hk (coordinateRatioSection R ι k i) := by
  simpa only [coordinateRatioSection_eq_homogeneousChartSection, Nat.cast_one, zpow_neg_one]
    using homogeneousChartSection_transition R ι 1 (coordinatePower R ι 1 i) j k hj hk

/-- A coordinate ratio restricted to a subopen cuts out its actual intersection with the
distinguished coordinate chart. -/
theorem basicOpen_restrict_coordinateRatioSection (i j : ι)
    {V : (ProjectiveSpace R ι).Opens} (hj : V ≤ coordinateOpen R ι j) :
    (ProjectiveSpace R ι).basicOpen
        (sectionRestrict (ProjectiveSpace R ι) hj (coordinateRatioSection R ι j i)) =
      V ⊓ coordinateOpen R ι i := by
  change (ProjectiveSpace R ι).basicOpen
    ((ProjectiveSpace R ι).presheaf.map (homOfLE hj).op (coordinateRatioSection R ι j i)) = _
  rw [Scheme.basicOpen_res, basicOpen_coordinateRatioSection, ← inf_assoc,
    inf_eq_left.mpr hj]

/-- The coordinate-ratio transition equation in the multiplication direction used for
target sections of a negative twist. -/
theorem coordinateRatioSection_transition_mul (i j k : ι)
    {V : (ProjectiveSpace R ι).Opens} (hj : V ≤ coordinateOpen R ι j)
    (hk : V ≤ coordinateOpen R ι k) :
    sectionRestrict (ProjectiveSpace R ι) hk (coordinateRatioSection R ι k i) =
      (coordinateTransitionOn R ι j k hj hk).val *
        sectionRestrict (ProjectiveSpace R ι) hj (coordinateRatioSection R ι j i) := by
  rw [coordinateRatioSection_transition R ι i j k hj hk, ← mul_assoc]
  have hu : (coordinateTransitionOn R ι j k hj hk).val *
      ((coordinateTransitionOn R ι j k hj hk)⁻¹).val = 1 :=
    (coordinateTransitionOn R ι j k hj hk).val_inv
  rw [hu, one_mul]

/-- Powers of the original transition unit commute with every actual common-open restriction. -/
theorem coordinateTransitionOn_pow_restrict (j k : ι) (n : ℕ)
    {V W : (ProjectiveSpace R ι).Opens} (h : V ≤ W)
    (hj : W ≤ coordinateOpen R ι j) (hk : W ≤ coordinateOpen R ι k) :
    sectionRestrict (ProjectiveSpace R ι) h
        ((coordinateTransitionOn R ι j k hj hk ^ n).val) =
      (coordinateTransitionOn R ι j k (h.trans hj) (h.trans hk) ^ n).val := by
  change (Units.map (sectionRestrict (ProjectiveSpace R ι) h).toMonoidHom
    (coordinateTransitionOn R ι j k hj hk ^ n)).val = _
  rw [map_pow, coordinateTransitionOn_restrict]

variable (M)

omit [M.IsQuasicoherent] in
/-- A chosen actual numerator equation restricts unchanged to every smaller common open. -/
theorem coordinateChartNumerator_restrict (i j : ι) (N : ℕ)
    (s : Γ(M, coordinateOpen R ι i)) (t : Γ(M, coordinateOpen R ι j))
    (ht : M.presheaf.map (homOfLE (inf_le_left :
      coordinateOpen R ι j ⊓ coordinateOpen R ι i ≤ coordinateOpen R ι j)).op t =
      ((ProjectiveSpace R ι).presheaf.map (homOfLE (inf_le_left :
        coordinateOpen R ι j ⊓ coordinateOpen R ι i ≤ coordinateOpen R ι j)).op
          (coordinateRatioSection R ι j i)) ^ N •
            M.presheaf.map (homOfLE (inf_le_right :
              coordinateOpen R ι j ⊓ coordinateOpen R ι i ≤ coordinateOpen R ι i)).op s)
    (V : (ProjectiveSpace R ι).Opens) (hj : V ≤ coordinateOpen R ι j)
    (hi : V ≤ coordinateOpen R ι i) :
    M.presheaf.map (homOfLE hj).op t =
      (sectionRestrict (ProjectiveSpace R ι) hj (coordinateRatioSection R ι j i)) ^ N •
        M.presheaf.map (homOfLE hi).op s := by
  have h := congrArg (M.presheaf.map (homOfLE (le_inf hj hi)).op) ht
  rw [Scheme.Modules.map_smul, map_pow] at h
  simpa only [← Functor.map_comp_apply, ← op_comp, homOfLE_comp, sectionRestrict] using h

end AlgebraicGeometry.ProjectiveSpace
