/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.BaseChangeSource
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.LocalCoordinates
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Twisting

/-!
# Original binary-form coordinates under arbitrary coefficient base change

The actual source comparison preserves the original source charts, factor
ratios and product coefficients, as sections over arbitrary base rings.
The proof uses the original coefficient ring homomorphism throughout.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace Opposite MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.Scheme.Modules.Invertible

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Original projective coordinate ratios pull back under the original coefficient map
on every compatible original source subopen. -/
theorem map_appLE_coordinateRatioSection (σ : R →+* S) (I : Type u) (a j : I)
    (V : (ProjectiveSpace S I).Opens) (hV : V ≤ coordinateOpen S I a) :
    ((ProjectiveSpace.map σ I).appLE (coordinateOpen R I a) V
      (hV.trans (map_preimage_coordinateOpen σ I a).ge))
        (coordinateRatioSection R I a j) =
      sectionRestrict (ProjectiveSpace S I) hV (coordinateRatioSection S I a j) := by
  have hV' : V ≤ Proj.basicOpen (homogeneousSubmodule I S) (gradedMap σ (X a)) :=
    by rw [show gradedMap σ (X a) = X a by simp]; exact hV
  have h₁ := ConcreteCategory.congr_hom
    ((ProjectiveSpace.map σ I).appLE_map
      (le_rfl : Proj.basicOpen (homogeneousSubmodule I S) (gradedMap σ (X a)) ≤
        ProjectiveSpace.map σ I ⁻¹ᵁ coordinateOpen R I a) (homOfLE hV').op)
    (coordinateRatioSection R I a j)
  have h₂ := ConcreteCategory.congr_hom
    (awayToSection_comp_appLE_map σ I (X a) (isHomogeneous_X R a)) (coordinateRatio R I a j)
  change (Proj.awayToSection (homogeneousSubmodule I R) (X a) ≫
    (ProjectiveSpace.map σ I).appLE (coordinateOpen R I a)
      (Proj.basicOpen (homogeneousSubmodule I S) (gradedMap σ (X a))) le_rfl).hom
        (coordinateRatio R I a j) = _ at h₂
  refine h₁.symm.trans ?_
  change sectionRestrict (ProjectiveSpace S I) hV'
    ((Proj.awayToSection (homogeneousSubmodule I R) (X a) ≫
      (ProjectiveSpace.map σ I).appLE (coordinateOpen R I a)
        (Proj.basicOpen (homogeneousSubmodule I S) (gradedMap σ (X a))) le_rfl).hom
          (coordinateRatio R I a j)) = _
  rw [h₂]
  change sectionRestrict (ProjectiveSpace S I) hV'
      ((Proj.awayToSection (homogeneousSubmodule I S) (gradedMap σ (X a))).hom
        (Away.map (gradedMap σ) (X a) (coordinateRatio R I a j))) =
    sectionRestrict (ProjectiveSpace S I) hV
      ((Proj.awayToSection (homogeneousSubmodule I S) (X a)).hom (coordinateRatio S I a j))
  rw [coordinateRatio, coordinateRatio, Away.map_mk]
  exact sectionRestrict_awayToSection_congr I (by simp) (by simp) _ _ _ _ hV' hV

/-- Pulling a native coordinate ratio through a composite is the original
section-ring composite, on the same displayed source subopen. -/
theorem ratioOn_comp_appLE {A I : Type u} [CommRing A] {X Y : Scheme.{u}}
    (g : X ⟶ Y) (f : Y ⟶ ProjectiveSpace A I) (a j : I)
    (U : Y.Opens) (hU : U ≤ f ⁻¹ᵁ coordinateOpen A I a)
    (V : X.Opens) (hV : V ≤ g ⁻¹ᵁ U) :
    (g.appLE U V hV) (ratioOn f a j U hU) =
      ratioOn (g ≫ f) a j V
        (hV.trans ((Opens.map g.base).map (homOfLE hU)).le) :=
  ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE g f
    (coordinateOpen A I a) U V hU hV) (coordinateRatioSection A I a j)

/-- The actual source comparison has the same original factor-coordinate chart preimages. -/
theorem sourceBaseChangeMap_preimage_sourceOpen (σ : R →+* S) (n : ℕ) (a : Chart.{u} n) :
    sourceBaseChangeMap σ n ⁻¹ᵁ sourceOpen R n a = sourceOpen S n a := by
  ext x
  change sourceBaseChangeMap σ n x ∈ ((sourceOpen R n a : (source R n).Opens) :
    Set (source R n)) ↔ x ∈ ((sourceOpen S n a : (source S n).Opens) : Set (source S n))
  rw [sourceOpen, sourceOpen, Opens.coe_iInf, Opens.coe_iInf]
  simp only [Set.mem_iInter]
  apply forall_congr'
  intro i
  change x ∈ (sourceBaseChangeMap σ n ≫ liftedProjection R n i) ⁻¹ᵁ
      coordinateOpen R (ULift.{u} (Fin 2)) (a i) ↔
    x ∈ liftedProjection S n i ⁻¹ᵁ coordinateOpen S (ULift.{u} (Fin 2)) (a i)
  rw [sourceBaseChangeMap_liftedProjection, Scheme.Hom.comp_preimage,
    map_preimage_coordinateOpen]

/-- The actual original source-chart section map preserves every original factor ratio. -/
theorem sourceBaseChangeMap_appLE_localRatio (σ : R →+* S) (n : ℕ) (a : Chart.{u} n)
    (i : Fin n) (j : ULift.{u} (Fin 2)) :
    (sourceBaseChangeMap σ n |>.appLE (sourceOpen R n a) (sourceOpen S n a)
      (sourceBaseChangeMap_preimage_sourceOpen σ n a).ge)
        (localRatio R n a i j (sourceOpen R n a) le_rfl) =
      localRatio S n a i j (sourceOpen S n a) le_rfl := by
  have h₁ := ratioOn_comp_appLE (sourceBaseChangeMap σ n) (liftedProjection R n i)
    (a i) j (sourceOpen R n a) (sourceOpen_le_coordinate R n a i) (sourceOpen S n a)
    (sourceBaseChangeMap_preimage_sourceOpen σ n a).ge
  have h₂ := ratioOn_comp_appLE (liftedProjection S n i)
    (ProjectiveSpace.map σ (ULift.{u} (Fin 2))) (a i) j
    (coordinateOpen S (ULift.{u} (Fin 2)) (a i))
    (map_preimage_coordinateOpen σ (ULift.{u} (Fin 2)) (a i)).ge (sourceOpen S n a)
    (sourceOpen_le_coordinate S n a i)
  have hmap := map_appLE_coordinateRatioSection σ (ULift.{u} (Fin 2)) (a i) j
    (coordinateOpen S (ULift.{u} (Fin 2)) (a i)) le_rfl
  simp only [sectionRestrict_refl] at hmap
  change ratioOn (ProjectiveSpace.map σ (ULift.{u} (Fin 2))) (a i) j
    (coordinateOpen S (ULift.{u} (Fin 2)) (a i)) _ = _ at hmap
  rw [hmap] at h₂
  simp only [sourceBaseChangeMap_liftedProjection] at h₁
  simpa only [localRatio, ratioOn] using h₁.trans h₂.symm

/-- The original coefficient ring-map law identifies the actual pulled coefficient sections. -/
theorem sourceBaseChangeMap_appLE_localCoefficient (σ : R →+* S) (n : ℕ)
    (a : Chart.{u} n) (j : Fin (n + 1)) :
    (sourceBaseChangeMap σ n |>.appLE (sourceOpen R n a) (sourceOpen S n a)
      (sourceBaseChangeMap_preimage_sourceOpen σ n a).ge)
        (localCoefficient R n a (sourceOpen R n a) le_rfl j) =
      localCoefficient S n a (sourceOpen S n a) le_rfl j := by
  change (sourceBaseChangeMap σ n |>.appLE (sourceOpen R n a) (sourceOpen S n a)
      (sourceBaseChangeMap_preimage_sourceOpen σ n a).ge).hom
        (coefficient _ _ j) = _
  rw [← coefficient_map]
  simp only [sourceBaseChangeMap_appLE_localRatio, localCoefficient]

end AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct
