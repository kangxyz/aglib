/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.BaseChangeRefined
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.CoordinateHomExt

/-!
# Actual arbitrary base change of binary-form multiplication

The same original coefficient ring-map identity and the same original local
ratios identify the actual two scheme morphisms over arbitrary base rings.
The comparison retains nilpotent sections and every original structural map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct

universe u

/-- The original refined source open maps into its selected original coefficient chart. -/
theorem multiplication_refined_le (A : Type u) [CommRing A] (n : ℕ)
    (z : Chart.{u} n × ULift.{u} (Fin (n + 1))) :
    refinedOpen A n z ≤ multiplication A n ⁻¹ᵁ
      coordinateOpen A (ULift.{u} (Fin (n + 1))) z.2 :=
  (sectionFrames A n).le_map_preimage_selected (structureMap A n) z le_rfl

variable {R S : Type u} [CommRing R] [CommRing S]

theorem multiplication_targetBaseChange_refined_le (σ : R →+* S) (n : ℕ)
    (z : Chart.{u} n × ULift.{u} (Fin (n + 1))) :
    refinedOpen S n z ≤
      (multiplication S n ≫ ProjectiveSpace.map σ (ULift.{u} (Fin (n + 1)))) ⁻¹ᵁ
        coordinateOpen R (ULift.{u} (Fin (n + 1))) z.2 := by
  rw [Scheme.Hom.comp_preimage, map_preimage_coordinateOpen]
  exact multiplication_refined_le S n z

theorem multiplication_sourceBaseChange_refined_le (σ : R →+* S) (n : ℕ)
    (z : Chart.{u} n × ULift.{u} (Fin (n + 1))) :
    refinedOpen S n z ≤ (sourceBaseChangeMap σ n ≫ multiplication R n) ⁻¹ᵁ
      coordinateOpen R (ULift.{u} (Fin (n + 1))) z.2 :=
  (sourceBaseChangeMap_preimage_refinedOpen σ n z).ge.trans
    ((sourceBaseChangeMap σ n).preimage_mono (multiplication_refined_le R n z))

theorem multiplication_targetBaseChange_ratio (σ : R →+* S) (n : ℕ)
    (z : Chart.{u} n × ULift.{u} (Fin (n + 1))) (j : ULift.{u} (Fin (n + 1))) :
    ratioOn (multiplication S n ≫ ProjectiveSpace.map σ (ULift.{u} (Fin (n + 1))))
      z.2 j (refinedOpen S n z) (multiplication_targetBaseChange_refined_le σ n z) =
      ratioOn (multiplication S n) z.2 j (refinedOpen S n z)
        (multiplication_refined_le S n z) := by
  have h := ratioOn_comp_appLE (multiplication S n)
    (ProjectiveSpace.map σ (ULift.{u} (Fin (n + 1)))) z.2 j
    (coordinateOpen S (ULift.{u} (Fin (n + 1))) z.2)
    (map_preimage_coordinateOpen σ (ULift.{u} (Fin (n + 1))) z.2).ge
    (refinedOpen S n z) (multiplication_refined_le S n z)
  have hm := map_appLE_coordinateRatioSection σ (ULift.{u} (Fin (n + 1))) z.2 j
    (coordinateOpen S (ULift.{u} (Fin (n + 1))) z.2) le_rfl
  simp only [sectionRestrict_refl] at hm
  change ratioOn (ProjectiveSpace.map σ (ULift.{u} (Fin (n + 1)))) z.2 j
    (coordinateOpen S (ULift.{u} (Fin (n + 1))) z.2) _ = _ at hm
  rw [hm] at h
  exact h.symm

theorem multiplication_sourceBaseChange_ratio (σ : R →+* S) (n : ℕ)
    (z : Chart.{u} n × ULift.{u} (Fin (n + 1))) (j : ULift.{u} (Fin (n + 1))) :
    (sourceBaseChangeMap σ n |>.appLE (refinedOpen R n z) (refinedOpen S n z)
      (sourceBaseChangeMap_preimage_refinedOpen σ n z).ge)
        (ratioOn (multiplication R n) z.2 j (refinedOpen R n z)
          (multiplication_refined_le R n z)) =
      ratioOn (sourceBaseChangeMap σ n ≫ multiplication R n) z.2 j (refinedOpen S n z)
        (multiplication_sourceBaseChange_refined_le σ n z) :=
  ratioOn_comp_appLE (sourceBaseChangeMap σ n) (multiplication R n) z.2 j
    (refinedOpen R n z) (multiplication_refined_le R n z) (refinedOpen S n z)
    (sourceBaseChangeMap_preimage_refinedOpen σ n z).ge

/-- Binary-form multiplication commutes with every original coefficient-ring
base change, as an equality of the actual original scheme morphisms. -/
theorem multiplication_baseChange (σ : R →+* S) (n : ℕ) :
    multiplication S n ≫ ProjectiveSpace.map σ (ULift.{u} (Fin (n + 1))) =
      sourceBaseChangeMap σ n ≫ multiplication R n := by
  have hbase :
      (multiplication S n ≫ ProjectiveSpace.map σ (ULift.{u} (Fin (n + 1)))) ≫
          toSpec R (ULift.{u} (Fin (n + 1))) =
        (sourceBaseChangeMap σ n ≫ multiplication R n) ≫
          toSpec R (ULift.{u} (Fin (n + 1))) := by
    calc
      _ = structureMap S n ≫ Spec.map (CommRingCat.ofHom σ) := by
        rw [Category.assoc, ProjectiveSpace.map_toSpec, ← Category.assoc, multiplication_over]
      _ = _ := by rw [Category.assoc, multiplication_over, sourceBaseChangeMap_over]
  apply hom_eq_of_cover_ratios (refinedOpen S n) (iSup_refinedOpen_eq_top S n) Prod.snd _ _
    (multiplication_targetBaseChange_refined_le σ n)
    (multiplication_sourceBaseChange_refined_le σ n) hbase
  intro z j
  have hu := selectedCoefficient_isUnit S n z
  rw [coefficientSection_frameOn] at hu
  apply hu.mul_left_cancel
  rw [multiplication_targetBaseChange_ratio]
  have hS := multiplication_coefficient_mul_ratio S n z (refinedOpen S n z) le_rfl j
  have hR := congrArg ((sourceBaseChangeMap σ n).appLE
      (refinedOpen R n z) (refinedOpen S n z)
      (sourceBaseChangeMap_preimage_refinedOpen σ n z).ge)
    (multiplication_coefficient_mul_ratio R n z (refinedOpen R n z) le_rfl j)
  rw [map_mul, sourceBaseChangeMap_appLE_refinedCoefficient σ n z z.2.down,
    sourceBaseChangeMap_appLE_refinedCoefficient σ n z j.down,
    multiplication_sourceBaseChange_ratio] at hR
  exact hS.trans hR.symm

/-- The actual binary-form morphism over the new coefficient ring is the
native categorical base change of the same original coefficient morphism. -/
theorem isPullback_multiplication_baseChange (σ : R →+* S) (n : ℕ) :
    CategoryTheory.IsPullback (sourceBaseChangeMap σ n) (multiplication S n)
      (multiplication R n) (ProjectiveSpace.map σ (ULift.{u} (Fin (n + 1)))) := by
  have h : CategoryTheory.IsPullback (sourceBaseChangeMap σ n)
      (multiplication S n ≫ toSpec S (ULift.{u} (Fin (n + 1))))
      (multiplication R n ≫ toSpec R (ULift.{u} (Fin (n + 1))))
      (Spec.map (CommRingCat.ofHom σ)) := by
    simpa only [multiplication_over] using isPullback_sourceBaseChangeMap σ n
  exact h.of_bot (multiplication_baseChange σ n).symm
    (ProjectiveSpace.isPullback_map σ (ULift.{u} (Fin (n + 1))))

/-- The comparison uses the original source map and the original multiplication
as its two unchanged categorical pullback projections. -/
def multiplicationBaseChangeIso (σ : R →+* S) (n : ℕ) :
    source S n ≅ CategoryTheory.Limits.pullback (multiplication R n)
      (ProjectiveSpace.map σ (ULift.{u} (Fin (n + 1)))) :=
  (isPullback_multiplication_baseChange σ n).isoPullback

@[reassoc (attr := simp)]
theorem multiplicationBaseChangeIso_hom_fst (σ : R →+* S) (n : ℕ) :
    (multiplicationBaseChangeIso σ n).hom ≫
      CategoryTheory.Limits.pullback.fst (multiplication R n)
        (ProjectiveSpace.map σ (ULift.{u} (Fin (n + 1)))) = sourceBaseChangeMap σ n :=
  (isPullback_multiplication_baseChange σ n).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem multiplicationBaseChangeIso_hom_snd (σ : R →+* S) (n : ℕ) :
    (multiplicationBaseChangeIso σ n).hom ≫
      CategoryTheory.Limits.pullback.snd (multiplication R n)
        (ProjectiveSpace.map σ (ULift.{u} (Fin (n + 1)))) = multiplication S n :=
  (isPullback_multiplication_baseChange σ n).isoPullback_hom_snd

end AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct
