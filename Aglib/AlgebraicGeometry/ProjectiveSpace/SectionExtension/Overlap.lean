/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.SectionExtension

/-!
# Correcting overlap torsion of projective section numerators

Local numerators with a common coordinate exponent agree with the original section on the
distinguished chart. Their discrepancy on every chart overlap therefore vanishes after
localization at the original coordinate ratio. Native affine quasicoherent localization
annihilates that discrepancy by a further power, with the original transition unit retained.
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

/-- The discrepancy between actual local numerator sections on a chart overlap is killed
by a power of the original distinguished coordinate ratio. -/
theorem exists_coordinateOverlapTorsion (i : ι) (N : ℕ)
    (s : Γ(M, coordinateOpen R ι i)) (t : ∀ j, Γ(M, coordinateOpen R ι j))
    (ht : ∀ j,
      M.presheaf.map (homOfLE (inf_le_left :
        coordinateOpen R ι j ⊓ coordinateOpen R ι i ≤ coordinateOpen R ι j)).op (t j) =
        ((ProjectiveSpace R ι).presheaf.map (homOfLE (inf_le_left :
          coordinateOpen R ι j ⊓ coordinateOpen R ι i ≤ coordinateOpen R ι j)).op
          (coordinateRatioSection R ι j i)) ^ N •
            M.presheaf.map (homOfLE (inf_le_right :
              coordinateOpen R ι j ⊓ coordinateOpen R ι i ≤ coordinateOpen R ι i)).op s)
    (j k : ι) :
    let W := coordinateOpen R ι j ⊓ coordinateOpen R ι k
    let f : Γ(ProjectiveSpace R ι, W) :=
      sectionRestrict (ProjectiveSpace R ι) inf_le_left (coordinateRatioSection R ι j i)
    ∃ K : ℕ, f ^ K •
      (M.presheaf.map (homOfLE (inf_le_right : W ≤ coordinateOpen R ι k)).op (t k) -
        (coordinateTransitionOn R ι j k (V := W) inf_le_left inf_le_right ^ N).val •
          M.presheaf.map (homOfLE (inf_le_left : W ≤ coordinateOpen R ι j)).op (t j)) = 0 := by
  let W := coordinateOpen R ι j ⊓ coordinateOpen R ι k
  let f : Γ(ProjectiveSpace R ι, W) :=
    sectionRestrict (ProjectiveSpace R ι) inf_le_left (coordinateRatioSection R ι j i)
  let D := (ProjectiveSpace R ι).basicOpen f
  let hDW : D ≤ W := (ProjectiveSpace R ι).basicOpen_le f
  let hj : D ≤ coordinateOpen R ι j := hDW.trans inf_le_left
  let hk : D ≤ coordinateOpen R ι k := hDW.trans inf_le_right
  have hi : D ≤ coordinateOpen R ι i := by
    change (ProjectiveSpace R ι).basicOpen
      (sectionRestrict (ProjectiveSpace R ι) (inf_le_left : W ≤ coordinateOpen R ι j)
        (coordinateRatioSection R ι j i)) ≤ coordinateOpen R ι i
    rw [basicOpen_restrict_coordinateRatioSection]
    exact inf_le_right
  have hjt := coordinateChartNumerator_restrict R ι M i j N s (t j) (ht j) D hj hi
  have hkt := coordinateChartNumerator_restrict R ι M i k N s (t k) (ht k) D hk hi
  have hcompat : M.presheaf.map (homOfLE hk).op (t k) =
      (coordinateTransitionOn R ι j k hj hk ^ N).val •
        M.presheaf.map (homOfLE hj).op (t j) := by
    rw [hkt, hjt, coordinateRatioSection_transition_mul R ι i j k hj hk,
      mul_pow, Units.val_pow_eq_pow_val, mul_smul]
  let δ : Γ(M, W) :=
    M.presheaf.map (homOfLE (inf_le_right : W ≤ coordinateOpen R ι k)).op (t k) -
      (coordinateTransitionOn R ι j k (V := W) inf_le_left inf_le_right ^ N).val •
        M.presheaf.map (homOfLE (inf_le_left : W ≤ coordinateOpen R ι j)).op (t j)
  have hz : M.presheaf.map (homOfLE hDW).op δ = 0 := by
    change M.presheaf.map (homOfLE hDW).op
      (M.presheaf.map (homOfLE (inf_le_right : W ≤ coordinateOpen R ι k)).op (t k) -
        (coordinateTransitionOn R ι j k (V := W) inf_le_left inf_le_right ^ N).val •
          M.presheaf.map (homOfLE (inf_le_left : W ≤ coordinateOpen R ι j)).op (t j)) = 0
    rw [map_sub, Scheme.Modules.map_smul]
    have hu : (ProjectiveSpace R ι).presheaf.map (homOfLE hDW).op
        ((coordinateTransitionOn R ι j k (V := W) inf_le_left inf_le_right ^ N).val) =
      (coordinateTransitionOn R ι j k hj hk ^ N).val :=
      coordinateTransitionOn_pow_restrict R ι j k N hDW inf_le_left inf_le_right
    rw [hu]
    have hleft : M.presheaf.map (homOfLE hDW).op
        (M.presheaf.map (homOfLE (inf_le_right : W ≤ coordinateOpen R ι k)).op (t k)) =
        M.presheaf.map (homOfLE hk).op (t k) :=
      (M.presheaf.map_comp_apply
        (homOfLE (inf_le_right : W ≤ coordinateOpen R ι k)).op (homOfLE hDW).op (t k)).symm
    have hright : M.presheaf.map (homOfLE hDW).op
        (M.presheaf.map (homOfLE (inf_le_left : W ≤ coordinateOpen R ι j)).op (t j)) =
        M.presheaf.map (homOfLE hj).op (t j) :=
      (M.presheaf.map_comp_apply
        (homOfLE (inf_le_left : W ≤ coordinateOpen R ι j)).op (homOfLE hDW).op (t j)).symm
    rw [hleft, hright]
    exact sub_eq_zero.mpr hcompat
  have hW : IsAffineOpen W :=
    (isAffineOpen_coordinateOpen R ι j).inf (isAffineOpen_coordinateOpen R ι k)
  exact exists_power_smul_eq_zero M hW f δ hz

/-- One further coordinate power corrects all original overlap discrepancies simultaneously
on a finite projective coordinate cover. -/
theorem exists_coordinateNumeratorCorrection [Finite ι] (i : ι) (N : ℕ)
    (s : Γ(M, coordinateOpen R ι i)) (t : ∀ j, Γ(M, coordinateOpen R ι j))
    (ht : ∀ j,
      M.presheaf.map (homOfLE (inf_le_left :
        coordinateOpen R ι j ⊓ coordinateOpen R ι i ≤ coordinateOpen R ι j)).op (t j) =
        ((ProjectiveSpace R ι).presheaf.map (homOfLE (inf_le_left :
          coordinateOpen R ι j ⊓ coordinateOpen R ι i ≤ coordinateOpen R ι j)).op
          (coordinateRatioSection R ι j i)) ^ N •
            M.presheaf.map (homOfLE (inf_le_right :
              coordinateOpen R ι j ⊓ coordinateOpen R ι i ≤ coordinateOpen R ι i)).op s) :
    ∃ K : ℕ, ∀ j k,
      let W := coordinateOpen R ι j ⊓ coordinateOpen R ι k
      M.presheaf.map (homOfLE (inf_le_right : W ≤ coordinateOpen R ι k)).op
          (coordinateRatioSection R ι k i ^ K • t k) =
        (coordinateTransitionOn R ι j k (V := W) inf_le_left inf_le_right ^ (N + K)).val •
          M.presheaf.map (homOfLE (inf_le_left : W ≤ coordinateOpen R ι j)).op
            (coordinateRatioSection R ι j i ^ K • t j) := by
  classical
  let := Fintype.ofFinite ι
  choose a ha using fun j k => exists_coordinateOverlapTorsion R ι M i N s t ht j k
  let K := Finset.univ.sup (fun jk : ι × ι => a jk.1 jk.2)
  refine ⟨K, ?_⟩
  intro j k
  let W := coordinateOpen R ι j ⊓ coordinateOpen R ι k
  let f : Γ(ProjectiveSpace R ι, W) :=
    sectionRestrict (ProjectiveSpace R ι) inf_le_left (coordinateRatioSection R ι j i)
  let u := coordinateTransitionOn R ι j k (V := W) inf_le_left inf_le_right
  let δ : Γ(M, W) :=
    M.presheaf.map (homOfLE (inf_le_right : W ≤ coordinateOpen R ι k)).op (t k) -
      (u ^ N).val •
        M.presheaf.map (homOfLE (inf_le_left : W ≤ coordinateOpen R ι j)).op (t j)
  have hab : a j k ≤ K :=
    Finset.le_sup (f := fun jk : ι × ι => a jk.1 jk.2) (Finset.mem_univ (j, k))
  have ha' : f ^ (a j k) • δ = 0 := ha j k
  have hkill : f ^ K • δ = 0 := by
    calc
      _ = f ^ (K - a j k) • (f ^ (a j k) • δ) := by
        rw [← mul_smul, ← pow_add, Nat.sub_add_cancel hab]
      _ = 0 := by rw [ha', smul_zero]
  have heq : f ^ K •
      M.presheaf.map (homOfLE (inf_le_right : W ≤ coordinateOpen R ι k)).op (t k) =
      f ^ K • ((u ^ N).val •
        M.presheaf.map (homOfLE (inf_le_left : W ≤ coordinateOpen R ι j)).op (t j)) := by
    apply sub_eq_zero.mp
    change f ^ K •
        M.presheaf.map (homOfLE (inf_le_right : W ≤ coordinateOpen R ι k)).op (t k) -
      f ^ K • ((u ^ N).val •
        M.presheaf.map (homOfLE (inf_le_left : W ≤ coordinateOpen R ι j)).op (t j)) = 0
    rw [← smul_sub]
    exact hkill
  change M.presheaf.map (homOfLE (inf_le_right : W ≤ coordinateOpen R ι k)).op
      (coordinateRatioSection R ι k i ^ K • t k) =
    (u ^ (N + K)).val •
      M.presheaf.map (homOfLE (inf_le_left : W ≤ coordinateOpen R ι j)).op
        (coordinateRatioSection R ι j i ^ K • t j)
  rw [Scheme.Modules.map_smul, Scheme.Modules.map_smul, map_pow, map_pow]
  change (sectionRestrict (ProjectiveSpace R ι)
      (inf_le_right : W ≤ coordinateOpen R ι k) (coordinateRatioSection R ι k i)) ^ K •
      M.presheaf.map (homOfLE (inf_le_right : W ≤ coordinateOpen R ι k)).op (t k) =
    (u ^ (N + K)).val • (f ^ K •
      M.presheaf.map (homOfLE (inf_le_left : W ≤ coordinateOpen R ι j)).op (t j))
  rw [coordinateRatioSection_transition_mul R ι i j k (V := W) inf_le_left inf_le_right,
    mul_pow, mul_smul]
  change u.val ^ K • (f ^ K •
      M.presheaf.map (homOfLE (inf_le_right : W ≤ coordinateOpen R ι k)).op (t k)) =
    (u ^ (N + K)).val • (f ^ K •
      M.presheaf.map (homOfLE (inf_le_left : W ≤ coordinateOpen R ι j)).op (t j))
  rw [heq]
  simp only [Units.val_pow_eq_pow_val, ← mul_smul]
  congr 1
  rw [pow_add]
  ring

end AlgebraicGeometry.ProjectiveSpace
