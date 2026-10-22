/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.BaseChange
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.ProjectiveVariableChange
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer

/-!
# Integral equations and native minima for a specified Weierstrass curve

One native common denominator gives an actual integral equation over any domain,
with exact native change, discriminant, and pointed generic comparison. Over a
DVR, Mathlib's actual native minimum producer supplies the selected change;
its full admissible projective map gives the same original pointed generic cubic.
The abstract pointed genus-one presentation is a separate input.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open WeierstrassCurve.Projective WeierstrassCurve.VariableChange

namespace WeierstrassCurve.IntegralModel

universe u v

section Denominators

variable (R : Type u) [CommRing R] [IsDomain R]
variable {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F]
variable (W : WeierstrassCurve F)

/-- The five original coefficients, ordered by their weights `1, 2, 3, 4, 6`. -/
def coefficientFamily : Fin 5 → F :=
  ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

/-- One native non-zero-divisor denominator for all five original coefficients. -/
def denominator : nonZeroDivisors R :=
  IsLocalization.commonDenom (nonZeroDivisors R) Finset.univ (coefficientFamily W)

/-- The actual numerator supplied by the native common-denominator construction. -/
def numerator (i : Fin 5) : R :=
  IsLocalization.integerMultiple (nonZeroDivisors R) Finset.univ
    (coefficientFamily W) ⟨i, Finset.mem_univ i⟩

omit [IsDomain R] in
@[simp] lemma map_numerator (i : Fin 5) :
    algebraMap R F (numerator R W i) =
      algebraMap R F (denominator R W : R) * coefficientFamily W i := by
  simpa only [numerator, denominator, Submonoid.smul_def, Algebra.smul_def] using
    IsLocalization.map_integerMultiple (nonZeroDivisors R) Finset.univ
      (coefficientFamily W) ⟨i, Finset.mem_univ i⟩

lemma denominator_ne_zero : (denominator R W : R) ≠ 0 :=
  mem_nonZeroDivisors_iff_ne_zero.mp (denominator R W).property

lemma map_denominator_ne_zero : algebraMap R F (denominator R W : R) ≠ 0 := by
  intro h
  apply denominator_ne_zero R W
  apply IsFractionRing.injective R F
  simpa only [map_zero] using h

/-- The chosen common denominator as a unit of the supplied fraction field. -/
def denominatorUnit : Fˣ :=
  Units.mk0 (algebraMap R F (denominator R W : R)) (map_denominator_ne_zero R W)

/-- The native variable change with `u = d⁻¹` and zero translation and shear. -/
def denominatorChange : WeierstrassCurve.VariableChange F :=
  scalingChange (denominatorUnit R W)⁻¹

/-- The integral equation with coefficients `n₁, d n₂, d² n₃, d³ n₄, d⁵ n₆`. -/
def equation : WeierstrassCurve R where
  a₁ := numerator R W 0
  a₂ := (denominator R W : R) * numerator R W 1
  a₃ := (denominator R W : R) ^ 2 * numerator R W 2
  a₄ := (denominator R W : R) ^ 3 * numerator R W 3
  a₆ := (denominator R W : R) ^ 5 * numerator R W 4

omit [IsDomain R] in
/-- The actual five integral coefficients map to `dⁱ aᵢ` with weights `1, 2, 3, 4, 6`. -/
theorem map_equation_coefficients :
    algebraMap R F (equation R W).a₁ =
        algebraMap R F (denominator R W : R) * W.a₁ ∧
      algebraMap R F (equation R W).a₂ =
        algebraMap R F (denominator R W : R) ^ 2 * W.a₂ ∧
      algebraMap R F (equation R W).a₃ =
        algebraMap R F (denominator R W : R) ^ 3 * W.a₃ ∧
      algebraMap R F (equation R W).a₄ =
        algebraMap R F (denominator R W : R) ^ 4 * W.a₄ ∧
      algebraMap R F (equation R W).a₆ =
        algebraMap R F (denominator R W : R) ^ 6 * W.a₆ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [equation, map_mul, map_pow, coefficientFamily] <;> ring

/-- The generic equation is exactly the native change of the given original equation. -/
theorem equation_baseChange :
    (equation R W).map (algebraMap R F) = denominatorChange R W • W := by
  ext <;>
    simp [equation, denominatorChange, scalingChange, denominatorUnit,
      WeierstrassCurve.variableChange_def, coefficientFamily] <;> ring

/-- The discriminant scales in the native direction: the integral equation has `d¹² Δ`. -/
theorem map_equation_discriminant :
    algebraMap R F (equation R W).Δ =
      algebraMap R F (denominator R W : R) ^ 12 * W.Δ := by
  rw [← WeierstrassCurve.map_Δ, equation_baseChange, WeierstrassCurve.variableChange_Δ]
  simp [denominatorChange, scalingChange, denominatorUnit]

/-- Nonvanishing of the discriminant is preserved by this actual integral equation. -/
theorem equation_discriminant_ne_zero_iff : (equation R W).Δ ≠ 0 ↔ W.Δ ≠ 0 := by
  constructor
  · intro hV hW
    apply hV
    apply IsFractionRing.injective R F
    rw [map_zero, map_equation_discriminant, hW, mul_zero]
  · intro hW hV
    have h : algebraMap R F (equation R W).Δ ≠ 0 := by
      rw [map_equation_discriminant]
      exact mul_ne_zero (pow_ne_zero _ (map_denominator_ne_zero R W)) hW
    exact h (by rw [hV, map_zero])

/-- The forward affine `x` coordinate is `d⁻² x` in the native variable-change convention. -/
lemma denominatorChange_changeX (x : F) :
    WeierstrassCurve.VariableChange.changeX (denominatorChange R W) x =
      (algebraMap R F (denominator R W : R))⁻¹ ^ 2 * x := by
  simp [WeierstrassCurve.VariableChange.changeX, denominatorChange, scalingChange,
    denominatorUnit]

/-- The forward affine `y` coordinate is `d⁻³ y`, with zero shear and translation. -/
lemma denominatorChange_changeY (x y : F) :
    WeierstrassCurve.VariableChange.changeY (denominatorChange R W) x y =
      (algebraMap R F (denominator R W : R))⁻¹ ^ 3 * y := by
  simp [WeierstrassCurve.VariableChange.changeY, denominatorChange, scalingChange,
    denominatorUnit]

/-- The actual generic homogeneous pullback sends `X, Y, Z` to `d⁻²X, d⁻³Y, Z`. -/
lemma denominatorChange_projective_coordinate (i : Fin 3) :
    WeierstrassCurve.VariableChange.projectiveHomogeneous W (denominatorChange R W)
        (coordinate W i) =
      algebraMap F (homogeneousCoordinateRing (denominatorChange R W • W))
        ((algebraMap R F (denominator R W : R))⁻¹ ^ coordinateWeight i) *
          coordinate (denominatorChange R W • W) i := by
  have hu : (↑((denominatorChange R W).u) : F) =
      (algebraMap R F (denominator R W : R))⁻¹ := by
    simp [denominatorChange, scalingChange, denominatorUnit]
  have hr : (denominatorChange R W).r = 0 := rfl
  have hs : (denominatorChange R W).s = 0 := rfl
  have ht : (denominatorChange R W).t = 0 := rfl
  fin_cases i
  · change projectiveHomogeneous W (denominatorChange R W) (coordinate W 0) =
      algebraMap F (homogeneousCoordinateRing (denominatorChange R W • W))
        ((algebraMap R F (denominator R W : R))⁻¹ ^ 2) *
          coordinate (denominatorChange R W • W) 0
    rw [projectiveHomogeneous_x, hu, hr]
    simp
  · change projectiveHomogeneous W (denominatorChange R W) (coordinate W 1) =
      algebraMap F (homogeneousCoordinateRing (denominatorChange R W • W))
        ((algebraMap R F (denominator R W : R))⁻¹ ^ 3) *
          coordinate (denominatorChange R W • W) 1
    rw [projectiveHomogeneous_y, hu, hs, ht]
    simp
  · change projectiveHomogeneous W (denominatorChange R W) (coordinate W 2) =
      algebraMap F (homogeneousCoordinateRing (denominatorChange R W • W))
        ((algebraMap R F (denominator R W : R))⁻¹ ^ 0) *
          coordinate (denominatorChange R W • W) 2
    rw [projectiveHomogeneous_z]
    simp

/-- The actual pointed generic cubic of the integral equation is isomorphic to the given cubic. -/
def genericOverIso :
    curveOver ((equation R W).map (algebraMap R F)) ≅ curveOver W :=
  WeierstrassCurve.Projective.Translation.projectiveEquationCastOverIso
    ((equation R W).map (algebraMap R F)) (denominatorChange R W • W)
    (equation_baseChange R W) ≪≫
      WeierstrassCurve.VariableChange.projectiveOverIso W (denominatorChange R W)

/-- The forward generic arrow is the canonical equation cast followed by the
literal native variable-change Proj map. -/
lemma genericOverIso_hom :
    (genericOverIso R W).hom.left =
      (WeierstrassCurve.Projective.Translation.projectiveEquationCastIso
        ((equation R W).map (algebraMap R F)) (denominatorChange R W • W)
        (equation_baseChange R W)).hom ≫
          Proj.map (WeierstrassCurve.VariableChange.projectiveGraded W (denominatorChange R W))
            (WeierstrassCurve.VariableChange.projective_irrelevant W (denominatorChange R W)) := rfl

/-- The generic comparison retains the original fraction-field structural maps. -/
lemma genericOverIso_over :
    (genericOverIso R W).hom.left ≫ structureMap W =
      structureMap ((equation R W).map (algebraMap R F)) :=
  (genericOverIso R W).hom.w

/-- The generic comparison carries the actual original infinity section to infinity. -/
@[reassoc] lemma genericOverIso_infinity :
    infinitySection ((equation R W).map (algebraMap R F)) ≫
      (genericOverIso R W).hom.left = infinitySection W := by
  change infinitySection ((equation R W).map (algebraMap R F)) ≫
      (WeierstrassCurve.Projective.Translation.projectiveEquationCastIso
        ((equation R W).map (algebraMap R F)) (denominatorChange R W • W)
        (equation_baseChange R W)).hom ≫
      (WeierstrassCurve.VariableChange.projectiveIso W (denominatorChange R W)).hom = _
  rw [← Category.assoc,
    WeierstrassCurve.Projective.Translation.projectiveEquationCastIso_infinity,
    WeierstrassCurve.VariableChange.projectiveIso_infinity]

end Denominators

section Minimal

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F]
variable (W : WeierstrassCurve F)

/-- The actual native change selected by Mathlib's minimum-discriminant producer. -/
def minimalChange : WeierstrassCurve.VariableChange F :=
  (WeierstrassCurve.exists_isMinimal R W).choose

/-- The selected native equation satisfies the original native minimum predicate. -/
instance minimalChangeIsMinimal : WeierstrassCurve.IsMinimal R (minimalChange R W • W) :=
  (WeierstrassCurve.exists_isMinimal R W).choose_spec

/-- An actual integral equation for the selected native minimum, using its proved integrality. -/
def minimalEquation : WeierstrassCurve R :=
  WeierstrassCurve.integralModel R (minimalChange R W • W)

/-- The actual integral equation maps to the same native minimum selected from the original `W`. -/
lemma minimalEquation_baseChange :
    (minimalEquation R W).map (algebraMap R F) = minimalChange R W • W := by
  simpa only [minimalEquation, WeierstrassCurve.baseChange] using
    WeierstrassCurve.baseChange_integralModel_eq R (minimalChange R W • W)

/-- The mapped integral equation has the native minimum property, with its original guard. -/
instance minimalEquationGenericIsMinimal :
    WeierstrassCurve.IsMinimal R ((minimalEquation R W).map (algebraMap R F)) := by
  rw [minimalEquation_baseChange]
  infer_instance

/-- The original native change gives the literal pointed generic minimum comparison. -/
def minimalGenericOverIso :
    curveOver ((minimalEquation R W).map (algebraMap R F)) ≅ curveOver W :=
  WeierstrassCurve.Projective.Translation.projectiveEquationCastOverIso
    ((minimalEquation R W).map (algebraMap R F)) (minimalChange R W • W)
    (minimalEquation_baseChange R W) ≪≫
      WeierstrassCurve.VariableChange.projectiveOverIso W (minimalChange R W)

/-- The forward minimum comparison uses the actual native full-coordinate Proj pullback. -/
lemma minimalGenericOverIso_hom :
    (minimalGenericOverIso R W).hom.left =
      (WeierstrassCurve.Projective.Translation.projectiveEquationCastIso
        ((minimalEquation R W).map (algebraMap R F)) (minimalChange R W • W)
        (minimalEquation_baseChange R W)).hom ≫
          Proj.map (WeierstrassCurve.VariableChange.projectiveGraded W (minimalChange R W))
            (WeierstrassCurve.VariableChange.projective_irrelevant W (minimalChange R W)) := rfl

/-- The native minimum comparison retains the original fraction-field structural maps. -/
lemma minimalGenericOverIso_over :
    (minimalGenericOverIso R W).hom.left ≫ structureMap W =
      structureMap ((minimalEquation R W).map (algebraMap R F)) :=
  (minimalGenericOverIso R W).hom.w

/-- The minimum comparison preserves the original infinity section exactly. -/
@[reassoc] lemma minimalGenericOverIso_infinity :
    infinitySection ((minimalEquation R W).map (algebraMap R F)) ≫
      (minimalGenericOverIso R W).hom.left = infinitySection W := by
  change infinitySection ((minimalEquation R W).map (algebraMap R F)) ≫
      (WeierstrassCurve.Projective.Translation.projectiveEquationCastIso
        ((minimalEquation R W).map (algebraMap R F)) (minimalChange R W • W)
        (minimalEquation_baseChange R W)).hom ≫
      (WeierstrassCurve.VariableChange.projectiveIso W (minimalChange R W)).hom = _
  rw [← Category.assoc,
    WeierstrassCurve.Projective.Translation.projectiveEquationCastIso_infinity,
    WeierstrassCurve.VariableChange.projectiveIso_infinity]

/-- The minimum discriminant has exactly the native `u⁻¹²` scaling factor. -/
lemma map_minimalEquation_discriminant :
    algebraMap R F (minimalEquation R W).Δ =
      (↑((minimalChange R W).u⁻¹) : F) ^ 12 * W.Δ := by
  rw [← WeierstrassCurve.map_Δ, minimalEquation_baseChange,
    WeierstrassCurve.variableChange_Δ]

/-- Nonvanishing is retained in the actual integral minimum equation. -/
lemma minimalEquation_discriminant_ne_zero_iff :
    (minimalEquation R W).Δ ≠ 0 ↔ W.Δ ≠ 0 := by
  constructor
  · intro hV hW
    apply hV
    apply IsFractionRing.injective R F
    rw [map_zero, map_minimalEquation_discriminant, hW, mul_zero]
  · intro hW hV
    have hu : (↑((minimalChange R W).u⁻¹) : F) ≠ 0 :=
      ((minimalChange R W).u⁻¹).isUnit.ne_zero
    have h : algebraMap R F (minimalEquation R W).Δ ≠ 0 := by
      rw [map_minimalEquation_discriminant]
      exact mul_ne_zero (pow_ne_zero _ hu) hW
    exact h (by rw [hV, map_zero])

end Minimal

section MinimalComparison

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F]
variable {W W' : WeierstrassCurve F} [WeierstrassCurve.IsMinimal R W]
  [WeierstrassCurve.IsMinimal R W']

/-- Native minimal equations in the same specified admissible orbit have equal
multiplicative discriminant valuations. This equality also holds for zero discriminant. -/
lemma minimal_discriminant_valuation_eq (C : WeierstrassCurve.VariableChange F)
    (hC : C • W = W') :
    (IsDiscreteValuationRing.maximalIdeal R).valuation F W.Δ =
      (IsDiscreteValuationRing.maximalIdeal R).valuation F W'.Δ := by
  have hCinv : C⁻¹ • W' = W := by rw [← hC, inv_smul_smul]
  have hle : WeierstrassCurve.valuation_Δ_aux R W' ≤
      WeierstrassCurve.valuation_Δ_aux R W := by
    have h := le_of_not_gt
      ((WeierstrassCurve.IsMinimal.val_Δ_maximal (R := R) (W := W)).not_gt
        (j := C) (by rw [hC]; infer_instance))
    simpa only [one_smul, hC] using h
  have hge : WeierstrassCurve.valuation_Δ_aux R W ≤
      WeierstrassCurve.valuation_Δ_aux R W' := by
    have h := le_of_not_gt
      ((WeierstrassCurve.IsMinimal.val_Δ_maximal (R := R) (W := W')).not_gt
        (j := C⁻¹) (by rw [hCinv]; infer_instance))
    simpa only [one_smul, hCinv] using h
  have h := congrArg Subtype.val (le_antisymm hge hle)
  simpa only [WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral] using h

/-- For nonzero discriminant, a specified change between native minima has unit-valued scale. -/
lemma minimal_change_valuation_u_eq_one (C : WeierstrassCurve.VariableChange F)
    (hC : C • W = W') (hΔ : W.Δ ≠ 0) :
    (IsDiscreteValuationRing.maximalIdeal R).valuation F (C.u : F) = 1 := by
  let val := (IsDiscreteValuationRing.maximalIdeal R).valuation F
  have hval : val W.Δ = val W'.Δ := minimal_discriminant_valuation_eq R C hC
  rw [← hC, WeierstrassCurve.variableChange_Δ, map_mul, map_pow] at hval
  have hvalΔ : val W.Δ ≠ 0 := val.ne_zero_iff.mpr hΔ
  have hpow : val (↑(C.u⁻¹) : F) ^ 12 = 1 := by
    apply mul_right_cancel₀ hvalΔ
    simpa only [one_mul] using hval.symm
  have hinv : val (↑(C.u⁻¹) : F) = 1 :=
    (pow_eq_one_iff_of_nonneg zero_le (by decide : (12 : ℕ) ≠ 0)).mp hpow
  rw [Units.val_inv_eq_inv_val, map_inv₀] at hinv
  exact inv_eq_one.mp hinv

/-- Every specified change between native minima with nonzero discriminant
is the base change of an actual native change over the original DVR. -/
theorem minimal_change_descends (C : WeierstrassCurve.VariableChange F)
    (hC : C • W = W') (hΔ : W.Δ ≠ 0) :
    ∃ CR : WeierstrassCurve.VariableChange R, CR.baseChange F = C := by
  have hunit := minimal_change_valuation_u_eq_one R C hC hΔ
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_valuation_eq
    (A := R) (K := F) (1 : F) (C.u : F) (by simpa only [map_one] using hunit.symm)
  have hu' : algebraMap R F (u : R) = (C.u : F) := by
    simpa only [Units.smul_def, Algebra.smul_def, mul_one] using hu
  exact WeierstrassCurve.variableChange_integral_of_u_integral hC hu'

/-- The descended change retains both literal integral coefficient equations,
and its generic change is the originally specified one. -/
theorem minimal_integral_equations_change_descends
    (V V' : WeierstrassCurve R)
    [WeierstrassCurve.IsMinimal R (V.map (algebraMap R F))]
    [WeierstrassCurve.IsMinimal R (V'.map (algebraMap R F))]
    (C : WeierstrassCurve.VariableChange F)
    (hC : C • V.map (algebraMap R F) = V'.map (algebraMap R F))
    (hΔ : V.Δ ≠ 0) :
    ∃ CR : WeierstrassCurve.VariableChange R,
      CR.baseChange F = C ∧ CR • V = V' := by
  have hΔF : (V.map (algebraMap R F)).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ]
    exact fun h => hΔ ((IsFractionRing.injective R F) (by simpa only [map_zero] using h))
  obtain ⟨CR, hCR⟩ := minimal_change_descends R C hC hΔF
  refine ⟨CR, hCR, ?_⟩
  apply WeierstrassCurve.map_injective (IsFractionRing.injective R F)
  change (CR • V).map (algebraMap R F) = V'.map (algebraMap R F)
  have hCR' : CR.map (algebraMap R F) = C := hCR
  rw [← WeierstrassCurve.map_variableChange, hCR']
  exact hC

/-- The same descended change gives an actual pointed projective comparison over the original DVR.
Its defining equality retains the literal native Proj map of that change,
after the equation cast. -/
theorem minimal_integral_equations_pointed_iso
    (V V' : WeierstrassCurve R)
    [WeierstrassCurve.IsMinimal R (V.map (algebraMap R F))]
    [WeierstrassCurve.IsMinimal R (V'.map (algebraMap R F))]
    (C : WeierstrassCurve.VariableChange F)
    (hC : C • V.map (algebraMap R F) = V'.map (algebraMap R F))
    (hΔ : V.Δ ≠ 0) :
    ∃ (CR : WeierstrassCurve.VariableChange R) (hCR : CR • V = V')
      (E : curveOver V' ≅ curveOver V),
      CR.baseChange F = C ∧
        E = eqToIso (congrArg (fun T : WeierstrassCurve R => curveOver T) hCR.symm) ≪≫
          WeierstrassCurve.VariableChange.projectiveOverIso V CR ∧
        infinitySection V' ≫ E.hom.left = infinitySection V := by
  obtain ⟨CR, hbase, hcoeff⟩ := minimal_integral_equations_change_descends R V V' C hC hΔ
  subst V'
  refine ⟨CR, rfl, WeierstrassCurve.VariableChange.projectiveOverIso V CR, hbase, ?_, ?_⟩
  · simp
  · exact WeierstrassCurve.VariableChange.projectiveIso_infinity V CR

end MinimalComparison

section SameUniverseGenericFibre

open CategoryTheory.Limits

variable (R : Type u) [CommRing R]
variable {F : Type u} [Field F] [Algebra R F]

/-- The existing canonical coefficient-base-change isomorphism over its coefficient-field base.
This wrapper retains the existing same-universe boundary of the native pullback interface. -/
def coefficientBaseChangeOverIso (V : WeierstrassCurve R) :
    curveOver (V.map (algebraMap R F)) ≅
      Over.mk (pullback.snd (structureMap V)
        (Spec.map (CommRingCat.ofHom (algebraMap R F)))) :=
  Over.isoMk (coefficientBaseChangeIso (S := F) V)
    (coefficientBaseChangeIso_hom_snd (S := F) V)

variable [IsDomain R] [IsFractionRing R F] (W : WeierstrassCurve F)

/-- The actual categorical generic fibre of the denominator-cleared equation
is the original cubic. -/
def genericFibreOverIso :
    Over.mk (pullback.snd (structureMap (equation R W))
      (Spec.map (CommRingCat.ofHom (algebraMap R F)))) ≅ curveOver W :=
  (coefficientBaseChangeOverIso R (equation R W)).symm ≪≫ genericOverIso R W

/-- The literal base-changed integral infinity section maps to the original infinity section. -/
@[reassoc] lemma genericFibreOverIso_infinity :
    baseChangedInfinitySection (S := F) (equation R W) ≫
      (genericFibreOverIso R W).hom.left = infinitySection W := by
  let e : scheme ((equation R W).map (algebraMap R F)) ≅
      pullback (structureMap (equation R W))
        (Spec.map (CommRingCat.ofHom (algebraMap R F))) :=
    coefficientBaseChangeIso (S := F) (equation R W)
  have he : infinitySection ((equation R W).map (algebraMap R F)) ≫ e.hom =
      baseChangedInfinitySection (S := F) (equation R W) := by
    simpa only [e, WeierstrassCurve.baseChange] using
      coefficientBaseChangeIso_pointed (S := F) (equation R W)
  change baseChangedInfinitySection (S := F) (equation R W) ≫
      e.inv ≫ (genericOverIso R W).hom.left = _
  rw [← he, Category.assoc, Iso.hom_inv_id_assoc]
  exact genericOverIso_infinity R W

variable [IsDiscreteValuationRing R]

/-- The native minimum equation also has an actual categorical pointed generic-fibre comparison. -/
def minimalGenericFibreOverIso :
    Over.mk (pullback.snd (structureMap (minimalEquation R W))
      (Spec.map (CommRingCat.ofHom (algebraMap R F)))) ≅ curveOver W :=
  (coefficientBaseChangeOverIso R (minimalEquation R W)).symm ≪≫ minimalGenericOverIso R W

@[reassoc] lemma minimalGenericFibreOverIso_infinity :
    baseChangedInfinitySection (S := F) (minimalEquation R W) ≫
      (minimalGenericFibreOverIso R W).hom.left = infinitySection W := by
  let e : scheme ((minimalEquation R W).map (algebraMap R F)) ≅
      pullback (structureMap (minimalEquation R W))
        (Spec.map (CommRingCat.ofHom (algebraMap R F))) :=
    coefficientBaseChangeIso (S := F) (minimalEquation R W)
  have he : infinitySection ((minimalEquation R W).map (algebraMap R F)) ≫ e.hom =
      baseChangedInfinitySection (S := F) (minimalEquation R W) := by
    simpa only [e, WeierstrassCurve.baseChange] using
      coefficientBaseChangeIso_pointed (S := F) (minimalEquation R W)
  change baseChangedInfinitySection (S := F) (minimalEquation R W) ≫
      e.inv ≫ (minimalGenericOverIso R W).hom.left = _
  rw [← he, Category.assoc, Iso.hom_inv_id_assoc]
  exact minimalGenericOverIso_infinity R W

end SameUniverseGenericFibre

end WeierstrassCurve.IntegralModel
