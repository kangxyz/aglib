/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.ProductPoints
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Map
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.CoefficientPolynomial

/-!
# Evaluation on the original normalized product points

The original source-chart ring map sends each pulled factor ratio to its
original normalized field coordinate. Consequently it sends every original
product coefficient to the same coefficient of the original factor vectors.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Field

universe u

private theorem ratioOn_pullback {R I : Type u} [CommRing R]
    {Y T : Scheme.{u}} (g : T ⟶ Y) (f : Y ⟶ ProjectiveSpace R I) (a j : I)
    (U : Y.Opens) (hU : U ≤ f ⁻¹ᵁ coordinateOpen R I a)
    (W : T.Opens) (hW : W ≤ g ⁻¹ᵁ U) :
    (g.appLE U W hW) (ratioOn f a j U hU) =
      ratioOn (g ≫ f) a j W
        (hW.trans ((Opens.map g.base).map (homOfLE hU)).le) := by
  exact ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE g f
    (coordinateOpen R I a) U W hU hW) (coordinateRatioSection R I a j)

private theorem basicOpen_appLE {Y T : Scheme.{u}} (g : T ⟶ Y)
    (U : Y.Opens) (W : T.Opens) (hW : W ≤ g ⁻¹ᵁ U) (r : Γ(Y, U)) :
    T.basicOpen ((g.appLE U W hW) r) = W ⊓ g ⁻¹ᵁ Y.basicOpen r := by
  change T.basicOpen (T.presheaf.map (homOfLE hW).op ((g.app U) r)) = _
  rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]

variable {R K : Type u} [CommRing R] [Field K] {n : ℕ}

/-- The original factor-coordinate chart selected by the normalized parameter family. -/
def pointChart (a : Fin n → Option K) : Chart.{u} n :=
  fun i => factorCoordinate (a i)

/-- The whole original field scheme maps into the selected original source chart. -/
theorem sourcePoint_preimage_chart (β : R →+* K) (a : Fin n → Option K) :
    ⊤ ≤ sourcePoint β a ⁻¹ᵁ sourceOpen R n (pointChart a) := by
  intro x _
  change sourcePoint β a x ∈ ((sourceOpen R n (pointChart a) : (source R n).Opens) :
    Set (source R n))
  rw [sourceOpen, Opens.coe_iInf]
  apply Set.mem_iInter.mpr
  intro i
  change (sourcePoint β a ≫ liftedProjection R n i) x ∈
    coordinateOpen R (ULift.{u} (Fin 2)) (factorCoordinate (a i))
  rw [sourcePoint_liftedProjection]
  exact point_preimage_selected β (factorVector (a i)) (factorCoordinate (a i)) _ trivial

/-- The actual field-valued section homomorphism on the same original source chart. -/
def pointChartEval (β : R →+* K) (a : Fin n → Option K) :
    Γ(source R n, sourceOpen R n (pointChart a)) →+* K :=
  (Scheme.ΓSpecIso (.of K)).hom.hom.comp
    (sourcePoint β a |>.appLE (sourceOpen R n (pointChart a)) ⊤
      (sourcePoint_preimage_chart β a)).hom

theorem pointChart_pullback_ratio (β : R →+* K) (a : Fin n → Option K)
    (i : Fin n) (j : ULift.{u} (Fin 2)) :
    (sourcePoint β a |>.appLE (sourceOpen R n (pointChart a)) ⊤
      (sourcePoint_preimage_chart β a))
        (localRatio R n (pointChart a) i j (sourceOpen R n (pointChart a)) le_rfl) =
      (Scheme.ΓSpecIso (.of K)).inv.hom (factorVector (a i) j) := by
  have h := ratioOn_pullback (sourcePoint β a) (liftedProjection R n i)
    (factorCoordinate (a i)) j (sourceOpen R n (pointChart a))
    (sourceOpen_le_coordinate R n (pointChart a) i) ⊤ (sourcePoint_preimage_chart β a)
  simpa only [localRatio, pointChart, sourcePoint_liftedProjection, liftedLinePoint,
    point_ratio, factorVector_selected, inv_one, mul_one] using h

@[simp]
theorem pointChartEval_ratio (β : R →+* K) (a : Fin n → Option K)
    (i : Fin n) (j : ULift.{u} (Fin 2)) :
    pointChartEval β a
        (localRatio R n (pointChart a) i j (sourceOpen R n (pointChart a)) le_rfl) =
      factorVector (a i) j := by
  change (Scheme.ΓSpecIso (.of K)).hom.hom
    ((sourcePoint β a |>.appLE (sourceOpen R n (pointChart a)) ⊤
      (sourcePoint_preimage_chart β a))
        (localRatio R n (pointChart a) i j (sourceOpen R n (pointChart a)) le_rfl)) = _
  rw [pointChart_pullback_ratio]
  exact (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.apply_symm_apply _

/-- Evaluating the original local coefficients gives the original normalized
product coefficients. -/
@[simp]
theorem pointChartEval_coefficient (β : R →+* K) (a : Fin n → Option K)
    (j : Fin (n + 1)) :
    pointChartEval β a
      (localCoefficient R n (pointChart a) (sourceOpen R n (pointChart a)) le_rfl j) =
        coefficient (fun i => first (a i)) (fun i => second (a i)) j := by
  rw [localCoefficient, ← coefficient_map]
  simp only [pointChartEval_ratio, factorVector_zero, factorVector_one]

theorem pointChart_pullback_coefficient (β : R →+* K) (a : Fin n → Option K)
    (j : Fin (n + 1)) :
    (sourcePoint β a |>.appLE (sourceOpen R n (pointChart a)) ⊤
      (sourcePoint_preimage_chart β a))
        (localCoefficient R n (pointChart a) (sourceOpen R n (pointChart a)) le_rfl j) =
      (Scheme.ΓSpecIso (.of K)).inv.hom
        (coefficient (fun i => first (a i)) (fun i => second (a i)) j) := by
  apply (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.injective
  exact (pointChartEval_coefficient β a j).trans
    ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.apply_symm_apply _).symm

/-- A normalized original product has some nonzero original displayed coefficient. -/
theorem exists_nonzero_coefficient (a : Fin n → Option K) :
    ∃ j : Fin (n + 1), coefficient (fun i => first (a i)) (fun i => second (a i)) j ≠ 0 := by
  let p := normalizedPolynomial a
  have hd : p.natDegree ≤ n := natDegree_polynomial_le _ _
  let j : Fin (n + 1) := ⟨n - p.natDegree, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  refine ⟨j, ?_⟩
  change p.coeff (n - (n - p.natDegree)) ≠ 0
  rw [Nat.sub_sub_self hd]
  exact Polynomial.leadingCoeff_ne_zero.mpr (normalizedPolynomial_ne_zero a)

/-- A nonzero original coefficient selects an actual original refined source open
containing the whole original field-valued product point. -/
theorem sourcePoint_preimage_refined (β : R →+* K) (a : Fin n → Option K)
    (j : Fin (n + 1))
    (hj : coefficient (fun i => first (a i)) (fun i => second (a i)) j ≠ 0) :
    ⊤ ≤ sourcePoint β a ⁻¹ᵁ refinedOpen R n (pointChart a, ULift.up j) := by
  have hu := (isUnit_iff_ne_zero.mpr hj).map (Scheme.ΓSpecIso (.of K)).inv.hom
  rw [← pointChart_pullback_coefficient β a j] at hu
  have hb := basicOpen_appLE (sourcePoint β a) (sourceOpen R n (pointChart a)) ⊤
    (sourcePoint_preimage_chart β a)
    (localCoefficient R n (pointChart a) (sourceOpen R n (pointChart a)) le_rfl j)
  rw [(Spec (.of K)).basicOpen_of_isUnit hu, top_inf_eq] at hb
  exact hb.le

theorem pointChart_pullback_coefficient_on_refined (β : R →+* K) (a : Fin n → Option K)
    (j₀ : Fin (n + 1))
    (hj : coefficient (fun i => first (a i)) (fun i => second (a i)) j₀ ≠ 0)
    (j : Fin (n + 1)) :
    (sourcePoint β a |>.appLE (refinedOpen R n (pointChart a, ULift.up j₀)) ⊤
      (sourcePoint_preimage_refined β a j₀ hj))
        (localCoefficient R n (pointChart a)
          (refinedOpen R n (pointChart a, ULift.up j₀))
          (refinedOpen_le R n (pointChart a, ULift.up j₀)) j) =
      (Scheme.ΓSpecIso (.of K)).inv.hom
        (coefficient (fun i => first (a i)) (fun i => second (a i)) j) := by
  have h := ConcreteCategory.congr_hom
    ((sourcePoint β a).map_appLE (sourcePoint_preimage_refined β a j₀ hj)
      (homOfLE (refinedOpen_le R n (pointChart a, ULift.up j₀))).op)
    (localCoefficient R n (pointChart a) (sourceOpen R n (pointChart a)) le_rfl j)
  change (sourcePoint β a |>.appLE (refinedOpen R n (pointChart a, ULift.up j₀)) ⊤
      (sourcePoint_preimage_refined β a j₀ hj))
      (sectionRestrict (source R n) (refinedOpen_le R n (pointChart a, ULift.up j₀))
        (localCoefficient R n (pointChart a) (sourceOpen R n (pointChart a)) le_rfl j)) = _ at h
  rw [localCoefficient_restrict] at h
  exact h.trans (pointChart_pullback_coefficient β a j)

/-- The actual product point maps into the original target chart selected by
any nonzero original product coefficient. -/
theorem sourcePoint_multiplication_preimage (β : R →+* K) (a : Fin n → Option K)
    (j₀ : Fin (n + 1))
    (hj : coefficient (fun i => first (a i)) (fun i => second (a i)) j₀ ≠ 0) :
    ⊤ ≤ (sourcePoint β a ≫ multiplication R n) ⁻¹ᵁ
      coordinateOpen R (ULift.{u} (Fin (n + 1))) (ULift.up j₀) :=
  (sourcePoint_preimage_refined β a j₀ hj).trans
    ((Opens.map (sourcePoint β a).base).map (homOfLE
      ((sectionFrames R n).le_map_preimage_selected (structureMap R n)
        (pointChart a, ULift.up j₀) le_rfl))).le

/-- The image's actual field-valued coordinate ratios satisfy the original
unnormalized coefficient relation. -/
theorem sourcePoint_multiplication_coefficient_mul_ratio (β : R →+* K)
    (a : Fin n → Option K) (j₀ : Fin (n + 1))
    (hj : coefficient (fun i => first (a i)) (fun i => second (a i)) j₀ ≠ 0)
    (j : ULift.{u} (Fin (n + 1))) :
    (Scheme.ΓSpecIso (.of K)).inv.hom
        (coefficient (fun i => first (a i)) (fun i => second (a i)) j₀) *
      ratioOn (sourcePoint β a ≫ multiplication R n) (ULift.up j₀) j ⊤
        (sourcePoint_multiplication_preimage β a j₀ hj) =
      (Scheme.ΓSpecIso (.of K)).inv.hom
        (coefficient (fun i => first (a i)) (fun i => second (a i)) j.down) := by
  let z : Chart.{u} n × ULift.{u} (Fin (n + 1)) := (pointChart a, ULift.up j₀)
  have h := congrArg ((sourcePoint β a).appLE (refinedOpen R n z) ⊤
    (sourcePoint_preimage_refined β a j₀ hj))
    (multiplication_coefficient_mul_ratio R n z (refinedOpen R n z) le_rfl j)
  rw [map_mul, pointChart_pullback_coefficient_on_refined β a j₀ hj j₀,
    pointChart_pullback_coefficient_on_refined β a j₀ hj j.down] at h
  have hr := ratioOn_pullback (sourcePoint β a) (multiplication R n) (ULift.up j₀) j
    (refinedOpen R n z)
    ((sectionFrames R n).le_map_preimage_selected (structureMap R n) z le_rfl)
    ⊤ (sourcePoint_preimage_refined β a j₀ hj)
  rw [hr] at h
  exact h

end AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Field
