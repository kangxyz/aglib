/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Line.LinearChange
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Original coordinate sections of the projective line over a ring

The literal chart sections are natural under the original coefficient map.
The original lower-unipotent coordinate change fixes infinity and translates
the affine parameter. All statements hold over arbitrary commutative rings.
The proofs use native homogeneous polynomial maps and the sole chart of
projective zero-space; no field, density, or reducedness hypothesis is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Matrix
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine.Sections

variable (R : Type u) [CommRing R]

/-- The literal section with parameter `a` in the original chart `i`. -/
def chartSection (i : Fin 2) (a : R) : Spec (.of R) ⟶ projectiveP1 R :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) ≫ chart R i

/-- The original quotient coordinate section `[0:1]`. -/
def infinity : Spec (.of R) ⟶ projectiveP1 R := chartSection R 1 0

/-- The original affine coordinate section `[1:a]`. -/
def affinePoint (a : R) : Spec (.of R) ⟶ projectiveP1 R := chartSection R 0 a

/-- The original structure triangle holds over every coefficient ring. -/
@[reassoc] theorem section_over (i : Fin 2) (a : R) :
    chartSection R i a ≫ structureMap R = 𝟙 _ := by
  rw [chartSection, Category.assoc, chart_over]
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  simp

@[reassoc] theorem infinity_over : infinity R ≫ structureMap R = 𝟙 _ :=
  section_over R 1 0

@[reassoc] theorem affinePoint_over (a : R) : affinePoint R a ≫ structureMap R = 𝟙 _ :=
  section_over R 0 a

/-- The original unipotent matrix whose affine action is addition of `t`. -/
def translationMatrix (t : R) : Matrix.GeneralLinearGroup (Fin 2) R where
  val := !![1, 0; t, 1]
  inv := !![1, 0; -t, 1]
  val_inv := by ext a b; fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext a b; fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem translationMatrix_zero : translationMatrix R 0 = 1 := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;> simp [translationMatrix]

/-- The original unipotent matrices add their parameters. -/
theorem translationMatrix_add (s t : R) :
    translationMatrix R (s + t) = translationMatrix R s * translationMatrix R t := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [translationMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Coefficient change retains every original entry of the unipotent matrix. -/
theorem translationMatrix_map {S : Type u} [CommRing S] (f : R →+* S) (t : R) :
    Matrix.GeneralLinearGroup.map f (translationMatrix R t) = translationMatrix S (f t) := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;> simp [translationMatrix, Matrix.GeneralLinearGroup.map]

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev ZeroIndex := PUnit.{u + 1}
private abbrev zeroGrading := MvPolynomial.homogeneousSubmodule ZeroIndex.{u} R
private abbrev zeroChartRing :=
  AlgebraicGeometry.ProjectiveSpace.coordinateRing R ZeroIndex.{u} PUnit.unit
private abbrev zeroChart : Spec (.of (zeroChartRing R)) ⟶ Proj (zeroGrading R) :=
  Proj.awayι (zeroGrading R) (MvPolynomial.X PUnit.unit)
    (MvPolynomial.isHomogeneous_X R PUnit.unit) Nat.zero_lt_one
private abbrev zeroCoefficient : R →+* zeroChartRing R :=
  AlgebraicGeometry.ProjectiveSpace.coordinateRingCoefficient R ZeroIndex.{u} PUnit.unit
private abbrev zeroStructure : Proj (zeroGrading R) ⟶ Spec (.of R) :=
  AlgebraicGeometry.ProjectiveSpace.toSpec R ZeroIndex.{u}

private instance zeroOther_isEmpty : IsEmpty {j : ZeroIndex.{u} // j ≠ PUnit.unit} :=
  ⟨fun j => j.2 (Subsingleton.elim _ _)⟩

private def zeroChartRingEquiv : zeroChartRing R ≃+* R :=
  (AlgebraicGeometry.ProjectiveSpace.coordinateRingEquivPolynomial
    R ZeroIndex.{u} PUnit.unit).trans (MvPolynomial.isEmptyRingEquiv R _)

private theorem zeroChartRingEquiv_symm :
    (zeroChartRingEquiv R).symm.toRingHom = zeroCoefficient R := by
  apply RingHom.ext
  intro r
  change AlgebraicGeometry.ProjectiveSpace.polynomialToCoordinateRing R ZeroIndex.{u}
    PUnit.unit ((MvPolynomial.isEmptyRingEquiv R _).symm r) = zeroCoefficient R r
  simp

private instance zeroChart_isIso : IsIso (zeroChart R) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [Proj.opensRange_awayι]
  simpa only [iSup_unique, AlgebraicGeometry.ProjectiveSpace.coordinateOpen] using
    (AlgebraicGeometry.ProjectiveSpace.iSup_coordinateOpen_eq_top R ZeroIndex.{u})

private theorem zeroChart_structure :
    zeroChart R ≫ zeroStructure R = Spec.map (CommRingCat.ofHom (zeroCoefficient R)) :=
  AlgebraicGeometry.ProjectiveSpace.coordinateChart_toSpec R ZeroIndex.{u} PUnit.unit

private instance zeroStructure_isIso : IsIso (zeroStructure R) := by
  have hc : IsIso (Spec.map (CommRingCat.ofHom (zeroCoefficient R))) := by
    rw [← zeroChartRingEquiv_symm]
    change IsIso (Scheme.Spec.mapIso (zeroChartRingEquiv R).toCommRingCatIso.symm.op).hom
    infer_instance
  have : IsIso (zeroChart R ≫ zeroStructure R) := by
    rw [zeroChart_structure]
    exact hc
  exact (isIso_comp_left_iff (zeroChart R) (zeroStructure R)).mp this

private def zeroIso : Proj (zeroGrading R) ≅ Spec (.of R) := asIso (zeroStructure R)

private def sectionGraded (i : Fin 2) (a : R) : grading R →+*ᵍ zeroGrading R where
  __ := MvPolynomial.eval₂Hom MvPolynomial.C
    (fun j => MvPolynomial.C (if j = i then 1 else a) * MvPolynomial.X PUnit.unit)
  map_mem := by
    intro n p hp
    change p.IsHomogeneous n at hp
    change (MvPolynomial.eval₂ MvPolynomial.C
      (fun j => MvPolynomial.C (if j = i then 1 else a) * MvPolynomial.X PUnit.unit)
      p).IsHomogeneous n
    simpa only [one_mul] using hp.eval₂ MvPolynomial.C _
      (fun r => isHomogeneous_C _ r)
      (fun _ => (isHomogeneous_X R PUnit.unit).C_mul _)

private theorem sectionGraded_C (i : Fin 2) (a r : R) :
    sectionGraded R i a (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [sectionGraded]

private theorem sectionGraded_X (i j : Fin 2) (a : R) :
    sectionGraded R i a (MvPolynomial.X j) =
      MvPolynomial.C (if j = i then 1 else a) * MvPolynomial.X PUnit.unit := by
  simp [sectionGraded]

private theorem sectionGraded_selected (i : Fin 2) (a : R) :
    sectionGraded R i a (MvPolynomial.X i) = MvPolynomial.X PUnit.unit := by
  simp [sectionGraded_X]

private theorem sectionGraded_irrelevant (i : Fin 2) (a : R) :
    HomogeneousIdeal.irrelevant (zeroGrading R) ≤
      (HomogeneousIdeal.irrelevant (grading R)).map (sectionGraded R i a) := by
  change (HomogeneousIdeal.irrelevant (zeroGrading R)).toIdeal ≤
    ((HomogeneousIdeal.irrelevant (grading R)).map (sectionGraded R i a)).toIdeal
  rw [MvPolynomial.irrelevant_homogeneousSubmodule_eq_idealOfVars,
    HomogeneousIdeal.toIdeal_map]
  change Ideal.span (Set.range (MvPolynomial.X : ZeroIndex.{u} → MvPolynomial ZeroIndex.{u} R)) ≤ _
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  cases j
  have hm : sectionGraded R i a (MvPolynomial.X i) ∈
      Ideal.map (sectionGraded R i a)
        (HomogeneousIdeal.irrelevant (grading R)).toIdeal :=
    Ideal.mem_map_of_mem (sectionGraded R i a)
      (HomogeneousIdeal.mem_irrelevant_of_mem (grading R) Nat.zero_lt_one
        (MvPolynomial.isHomogeneous_X R i))
  simpa only [SetLike.mem_coe, sectionGraded_selected] using hm

private def sectionProjective (i : Fin 2) (a : R) :
    Proj (zeroGrading R) ⟶ projectiveP1 R :=
  Proj.map (sectionGraded R i a) (sectionGraded_irrelevant R i a)

private def sectionAway (i : Fin 2) (a : R) : chartRing R i →+* zeroChartRing R :=
  HomogeneousLocalization.map (sectionGraded R i a)
    (P := Submonoid.powers (MvPolynomial.X i))
    (Q := Submonoid.powers (MvPolynomial.X PUnit.unit))
    (by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp [sectionGraded_selected]⟩)

private theorem sectionAway_square (i : Fin 2) (a : R) :
    zeroChart R ≫ sectionProjective R i a =
      Spec.map (CommRingCat.ofHom (sectionAway R i a)) ≫
        Proj.awayι (grading R) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one := by
  have H (x : MvPolynomial ZeroIndex.{u} R)
      (hx : x = sectionGraded R i a (MvPolynomial.X i))
      (hd : x ∈ zeroGrading R 1) :
      Proj.awayι (zeroGrading R) x hd Nat.zero_lt_one ≫ sectionProjective R i a =
        Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.map (sectionGraded R i a)
            (P := Submonoid.powers (MvPolynomial.X i)) (Q := Submonoid.powers x)
            (by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp [hx]⟩))) ≫
          Proj.awayι (grading R) (MvPolynomial.X i)
            (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one := by
    subst x
    exact Proj.awayι_comp_map (sectionGraded R i a) (sectionGraded_irrelevant R i a)
      Nat.zero_lt_one (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X R i)
  exact H (MvPolynomial.X PUnit.unit) (sectionGraded_selected R i a).symm
    (MvPolynomial.isHomogeneous_X R PUnit.unit)

private theorem sectionAway_constant (i : Fin 2) (a r : R) :
    sectionAway R i a (chartConstant R i r) = zeroCoefficient R r := by
  apply HomogeneousLocalization.val_injective
  change (HomogeneousLocalization.map (sectionGraded R i a) _
      (HomogeneousLocalization.mk ⟨0, constToGradeZero R r, 1, one_mem _⟩)).val = _
  rw [HomogeneousLocalization.map_mk]
  simp only [HomogeneousLocalization.val_mk]
  change Localization.mk (sectionGraded R i a (MvPolynomial.C r))
      ⟨sectionGraded R i a (1 : MvPolynomial (Fin 2) R), _⟩ =
    Localization.mk (MvPolynomial.C r) ⟨1, _⟩
  simp only [sectionGraded_C, map_one]

private theorem sectionAway_ratio (i : Fin 2) (a : R) :
    sectionAway R i a (chartRatio R i) = zeroCoefficient R a := by
  have hi : i.rev ≠ i := by fin_cases i <;> decide
  apply HomogeneousLocalization.val_injective
  simp only [sectionAway, chartRatio, HomogeneousLocalization.Away.mk,
    HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]
  change Localization.mk (sectionGraded R i a (MvPolynomial.X i.rev)) ⟨_, _⟩ =
    Localization.mk (MvPolynomial.C a) ⟨1, _⟩
  simp only [sectionGraded_X, ite_eq_right hi, pow_one]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

private theorem sectionAway_eq (i : Fin 2) (a : R) :
    sectionAway R i a = (zeroCoefficient R).comp
      ((Polynomial.evalRingHom a).comp (dehomogenize R i)) := by
  apply chartRing_hom_ext R i
  · intro r
    rw [sectionAway_constant]
    simp
  · rw [sectionAway_ratio]
    simp

private theorem section_eq_projective (i : Fin 2) (a : R) :
    chartSection R i a = (zeroIso R).inv ≫ sectionProjective R i a := by
  apply (cancel_epi (zeroIso R).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  apply (cancel_epi (zeroChart R)).mp
  change zeroChart R ≫ (zeroStructure R ≫ chartSection R i a) =
    zeroChart R ≫ sectionProjective R i a
  rw [← Category.assoc, zeroChart_structure, sectionAway_square, sectionAway_eq]
  simp only [chartSection, chart, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

private theorem sectionProjective_translation_infinity (t : R) :
    sectionProjective R 1 0 ≫ LinearChange.matrixMap R (translationMatrix R t) =
      sectionProjective R 1 0 := by
  have h : (sectionGraded R 1 0).comp
      (LinearChange.linearSubstitution R (translationMatrix R t : LinearChange.Matrix2 R)) =
      sectionGraded R 1 0 := by
    apply GradedRingHom.ext
    intro p
    have he : ((sectionGraded R 1 0).comp
        (LinearChange.linearSubstitution R
          (translationMatrix R t : LinearChange.Matrix2 R))).toRingHom =
        (sectionGraded R 1 0).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [sectionGraded_C]
      · intro j
        fin_cases j <;> simp [LinearChange.linearSubstitution_X, LinearChange.linearForm,
          translationMatrix, sectionGraded_C, sectionGraded_X]
    exact DFunLike.congr_fun he p
  unfold sectionProjective LinearChange.matrixMap
  rw [← Proj.map_comp]
  congr 1

private theorem sectionProjective_translation_affine (a t : R) :
    sectionProjective R 0 a ≫ LinearChange.matrixMap R (translationMatrix R t) =
      sectionProjective R 0 (a + t) := by
  have h : (sectionGraded R 0 a).comp
      (LinearChange.linearSubstitution R (translationMatrix R t : LinearChange.Matrix2 R)) =
      sectionGraded R 0 (a + t) := by
    apply GradedRingHom.ext
    intro p
    have he : ((sectionGraded R 0 a).comp
        (LinearChange.linearSubstitution R
          (translationMatrix R t : LinearChange.Matrix2 R))).toRingHom =
        (sectionGraded R 0 (a + t)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [sectionGraded_C]
      · intro j
        fin_cases j <;> simp [LinearChange.linearSubstitution_X, LinearChange.linearForm,
          translationMatrix, sectionGraded_C, sectionGraded_X, map_add, map_mul]
        ring
    exact DFunLike.congr_fun he p
  unfold sectionProjective LinearChange.matrixMap
  rw [← Proj.map_comp]
  congr 1

/-- The original lower-unipotent morphism fixes the literal infinity section. -/
@[reassoc] theorem infinity_translation (t : R) :
    infinity R ≫ LinearChange.matrixMap R (translationMatrix R t) = infinity R := by
  simp only [infinity, section_eq_projective, Category.assoc,
    sectionProjective_translation_infinity]

/-- The original lower-unipotent morphism translates the literal affine parameter. -/
@[reassoc] theorem affinePoint_translation (a t : R) :
    affinePoint R a ≫ LinearChange.matrixMap R (translationMatrix R t) =
      affinePoint R (a + t) := by
  simp only [affinePoint, section_eq_projective, Category.assoc,
    sectionProjective_translation_affine]

variable {R} {S : Type u} [CommRing S]

private theorem sectionProjective_coefficient (f : R →+* S) (i : Fin 2) (a : R) :
    sectionProjective S i (f a) ≫ LinearChange.coefficientMap f =
      AlgebraicGeometry.ProjectiveSpace.map f ZeroIndex.{u} ≫ sectionProjective R i a := by
  have h : (sectionGraded S i (f a)).comp (MvPolynomial.gradedMap f) =
      (MvPolynomial.gradedMap f).comp (sectionGraded R i a) := by
    apply GradedRingHom.ext
    intro p
    have he : ((sectionGraded S i (f a)).comp (MvPolynomial.gradedMap f)).toRingHom =
        ((MvPolynomial.gradedMap f).comp (sectionGraded R i a)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        change sectionGraded S i (f a) (MvPolynomial.map f (MvPolynomial.C r)) =
          MvPolynomial.map f (sectionGraded R i a (MvPolynomial.C r))
        simp only [MvPolynomial.map_C, sectionGraded_C]
      · intro j
        change sectionGraded S i (f a) (MvPolynomial.map f (MvPolynomial.X j)) =
          MvPolynomial.map f (sectionGraded R i a (MvPolynomial.X j))
        by_cases hji : j = i <;> simp [sectionGraded_X, hji]
    exact DFunLike.congr_fun he p
  unfold sectionProjective LinearChange.coefficientMap AlgebraicGeometry.ProjectiveSpace.map
  rw [← Proj.map_comp, ← Proj.map_comp]
  congr 1

private theorem zeroIso_coefficient (f : R →+* S) :
    (zeroIso S).inv ≫ AlgebraicGeometry.ProjectiveSpace.map f ZeroIndex.{u} =
      Spec.map (CommRingCat.ofHom f) ≫ (zeroIso R).inv := by
  apply (cancel_mono (zeroIso R).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (zeroIso S).inv ≫ AlgebraicGeometry.ProjectiveSpace.map f ZeroIndex.{u} ≫
      AlgebraicGeometry.ProjectiveSpace.toSpec R ZeroIndex.{u} = _
  rw [AlgebraicGeometry.ProjectiveSpace.map_toSpec]
  change (zeroIso S).inv ≫ (zeroIso S).hom ≫ Spec.map (CommRingCat.ofHom f) = _
  simp only [Iso.inv_hom_id_assoc]

/-- The literal chart section commutes with the original coefficient morphism. -/
@[reassoc] theorem section_coefficient (f : R →+* S) (i : Fin 2) (a : R) :
    chartSection S i (f a) ≫ LinearChange.coefficientMap f =
      Spec.map (CommRingCat.ofHom f) ≫ chartSection R i a := by
  rw [section_eq_projective, Category.assoc, sectionProjective_coefficient,
    ← Category.assoc, zeroIso_coefficient, Category.assoc, ← section_eq_projective]

/-- The original infinity section is natural over the original spectrum map. -/
@[reassoc] theorem infinity_coefficient (f : R →+* S) :
    infinity S ≫ LinearChange.coefficientMap f =
      Spec.map (CommRingCat.ofHom f) ≫ infinity R := by
  simpa only [infinity, map_zero] using section_coefficient f 1 0

/-- The original affine parameter is changed by the original coefficient homomorphism. -/
@[reassoc] theorem affinePoint_coefficient (f : R →+* S) (a : R) :
    affinePoint S (f a) ≫ LinearChange.coefficientMap f =
      Spec.map (CommRingCat.ofHom f) ≫ affinePoint R a :=
  section_coefficient f 0 a

/-- The literal affine coordinate section determines its original ring parameter. -/
theorem affinePoint_injective : Function.Injective (affinePoint R) := by
  intro a b h
  have he : Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom b)) :=
    (cancel_mono (chart R 0)).mp h
  have hr := Spec.map_injective he
  simpa using congrArg (fun f : CommRingCat.of R[X] ⟶ CommRingCat.of R =>
    f.hom Polynomial.X) hr

/-- The parameter of an actual section of the polynomial affine line. -/
def polynomialSectionParameter (f : Spec (.of R) ⟶ Spec (.of R[X])) : R :=
  (Spec.preimage f).hom Polynomial.X

/-- Every actual polynomial-line section is evaluation at its original parameter. -/
theorem polynomialSection_eq (f : Spec (.of R) ⟶ Spec (.of R[X]))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X])) = 𝟙 _) :
    f = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (polynomialSectionParameter f))) := by
  have hc : CommRingCat.ofHom (Polynomial.C : R →+* R[X]) ≫ Spec.preimage f = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, hf, Spec.map_id]
  have he : (Spec.preimage f).hom = Polynomial.evalRingHom (polynomialSectionParameter f) := by
    apply Polynomial.ringHom_ext
    · intro r
      simpa using congrArg (fun q : CommRingCat.of R ⟶ CommRingCat.of R => q.hom r) hc
    · simp [polynomialSectionParameter]
  exact (Spec.map_preimage f).symm.trans
    (congrArg (fun φ : R[X] →+* R => Spec.map (CommRingCat.ofHom φ)) he)

section TranslationOverlap

variable (R)

private abbrev translationSubstitution (t : R) :=
  LinearChange.linearSubstitution R (translationMatrix R t : LinearChange.Matrix2 R)

private abbrev translationForm (t : R) :=
  translationSubstitution R t (MvPolynomial.X (1 : Fin 2))

private theorem translationForm_homogeneous (t : R) :
    translationForm R t ∈ grading R 1 :=
  (translationSubstitution R t).map_mem (MvPolynomial.isHomogeneous_X R 1)

private theorem translationSubstitution_X_zero (t : R) :
    translationSubstitution R t (MvPolynomial.X 0) = MvPolynomial.X 0 := by
  simp [translationSubstitution, LinearChange.linearForm, translationMatrix]

/-- The exact denominator of the original unipotent change in chart one. -/
def translationOverlapPolynomial (t : R) : R[X] := 1 + Polynomial.C t * Polynomial.X

/-- The original principal localization on which chart one and its translate meet. -/
abbrev translationOverlapRing (t : R) := Localization.Away (translationOverlapPolynomial R t)

/-- The actual transformed chart-one coordinate in its principal localization. -/
def translationOverlapCoordinate (t : R) : translationOverlapRing R t :=
  algebraMap R[X] (translationOverlapRing R t) Polynomial.X *
    IsLocalization.Away.invSelf (translationOverlapPolynomial R t)

private abbrev translationHomogeneousOverlap (t : R) :=
  HomogeneousLocalization.Away (grading R) (MvPolynomial.X 1 * translationForm R t)

private def translationOverlapFromChart (t : R) :
    chartRing R 1 →+* translationHomogeneousOverlap R t :=
  HomogeneousLocalization.awayMap (grading R) (translationForm_homogeneous R t) rfl

private def translationOverlapFromChangedChart (t : R) :
    HomogeneousLocalization.Away (grading R) (translationForm R t) →+*
      translationHomogeneousOverlap R t :=
  HomogeneousLocalization.awayMap (grading R) (MvPolynomial.isHomogeneous_X R 1)
    (mul_comm _ _)

private abbrev translationHomogeneousDenominator (t : R) : chartRing R 1 :=
  HomogeneousLocalization.Away.isLocalizationElem (MvPolynomial.isHomogeneous_X R 1)
    (translationForm_homogeneous R t)

private theorem dehomogenize_translationDenominator (t : R) :
    dehomogenize R 1 (translationHomogeneousDenominator R t) =
      translationOverlapPolynomial R t := by
  simp only [translationHomogeneousDenominator, HomogeneousLocalization.Away.isLocalizationElem,
    pow_one, dehomogenize_mk]
  simp [translationForm, translationSubstitution, LinearChange.linearForm, translationMatrix,
    dehomogenizePolynomial, translationOverlapPolynomial, add_comm]

private instance translationOverlapAlgebra (t : R) :
    Algebra (chartRing R 1) (translationHomogeneousOverlap R t) :=
  (translationOverlapFromChart R t).toAlgebra

private instance translationOverlapLocalization (t : R) :
    IsLocalization.Away (translationHomogeneousDenominator R t)
      (translationHomogeneousOverlap R t) :=
  HomogeneousLocalization.Away.isLocalization_mul
    (MvPolynomial.isHomogeneous_X R 1) (translationForm_homogeneous R t) rfl (by decide)

private def translationOverlapValue (t : R) :
    translationHomogeneousOverlap R t →+* translationOverlapRing R t :=
  IsLocalization.Away.lift (translationHomogeneousDenominator R t)
    (g := (algebraMap R[X] (translationOverlapRing R t)).comp (dehomogenize R 1))
    (by
      rw [RingHom.comp_apply, dehomogenize_translationDenominator]
      exact IsLocalization.Away.algebraMap_isUnit _)

private theorem translationOverlapValue_fromChart (t : R) (x : chartRing R 1) :
    translationOverlapValue R t (translationOverlapFromChart R t x) =
      algebraMap R[X] (translationOverlapRing R t) (dehomogenize R 1 x) :=
  IsLocalization.Away.lift_eq _ _ x

private theorem translationOverlap_numerator_relation (t : R) :
    translationOverlapFromChart R t (translationHomogeneousDenominator R t) *
      translationOverlapFromChangedChart R t
        (HomogeneousLocalization.Away.map (translationSubstitution R t) (MvPolynomial.X 1)
          (chartRatio R 1)) =
      translationOverlapFromChart R t (chartRatio R 1) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, translationOverlapFromChart,
    translationOverlapFromChangedChart, translationHomogeneousDenominator,
    HomogeneousLocalization.Away.isLocalizationElem, chartRatio,
    HomogeneousLocalization.Away.map_mk, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul,
    show (1 : Fin 2).rev = 0 from rfl, pow_one, translationSubstitution_X_zero]
  ring

private theorem translationOverlapValue_changed_ratio (t : R) :
    translationOverlapValue R t
      (translationOverlapFromChangedChart R t
        (HomogeneousLocalization.Away.map (translationSubstitution R t) (MvPolynomial.X 1)
          (chartRatio R 1))) = translationOverlapCoordinate R t := by
  apply (IsLocalization.Away.algebraMap_isUnit
    (S := translationOverlapRing R t) (translationOverlapPolynomial R t)).mul_left_cancel
  have h := congrArg (translationOverlapValue R t) (translationOverlap_numerator_relation R t)
  rw [map_mul, translationOverlapValue_fromChart, dehomogenize_translationDenominator,
    translationOverlapValue_fromChart, dehomogenize_chartRatio] at h
  rw [h, translationOverlapCoordinate, mul_left_comm,
    IsLocalization.Away.mul_invSelf, mul_one]

private theorem translationOverlapValue_changed_constant (t r : R) :
    translationOverlapValue R t
      (translationOverlapFromChangedChart R t
        (HomogeneousLocalization.Away.map (translationSubstitution R t) (MvPolynomial.X 1)
          (chartConstant R 1 r))) =
      algebraMap R[X] (translationOverlapRing R t) (Polynomial.C r) := by
  have h : translationOverlapFromChangedChart R t
      (HomogeneousLocalization.Away.map (translationSubstitution R t) (MvPolynomial.X 1)
        (chartConstant R 1 r)) =
      translationOverlapFromChart R t (chartConstant R 1 r) := by
    simp only [chartConstant, RingHom.comp_apply, translationSubstitution,
      LinearChange.linearSubstitution_away_constant, translationOverlapFromChangedChart,
      translationOverlapFromChart, HomogeneousLocalization.awayMap_fromZeroRingHom]
  rw [h, translationOverlapValue_fromChart, dehomogenize_chartConstant]

/-- The literal polynomial map of the original unipotent transition on its chart-one overlap. -/
def translationOverlapMap (t : R) : R[X] →+* translationOverlapRing R t :=
  Polynomial.eval₂RingHom
    ((algebraMap R[X] (translationOverlapRing R t)).comp Polynomial.C)
    (translationOverlapCoordinate R t)

private theorem translationOverlapValue_changed (t : R) :
    (translationOverlapValue R t).comp
      ((translationOverlapFromChangedChart R t).comp
        (HomogeneousLocalization.Away.map (translationSubstitution R t) (MvPolynomial.X 1))) =
      (translationOverlapMap R t).comp (dehomogenize R 1) := by
  apply chartRing_hom_ext R 1
  · intro r
    simpa [translationOverlapMap] using translationOverlapValue_changed_constant R t r
  · simpa [translationOverlapMap] using translationOverlapValue_changed_ratio R t

/-- The actual Proj transition has coordinate `x/(1+t*x)` on the original principal overlap.
The proof compares its native homogeneous localization maps and does not use density. -/
@[reassoc] theorem chart_one_translation_overlap (t : R) :
    Spec.map (CommRingCat.ofHom (algebraMap R[X] (translationOverlapRing R t))) ≫
      chart R 1 ≫ LinearChange.matrixMap R (translationMatrix R t) =
      Spec.map (CommRingCat.ofHom (translationOverlapMap R t)) ≫ chart R 1 := by
  have he : (translationOverlapValue R t).comp (translationOverlapFromChart R t) =
      (algebraMap R[X] (translationOverlapRing R t)).comp (dehomogenize R 1) :=
    RingHom.ext (translationOverlapValue_fromChart R t)
  have hs : Spec.map (CommRingCat.ofHom (algebraMap R[X] (translationOverlapRing R t))) ≫
      chart R 1 = Spec.map (CommRingCat.ofHom (translationOverlapValue R t)) ≫
        Spec.map (CommRingCat.ofHom (translationOverlapFromChart R t)) ≫
          Proj.awayι (grading R) (MvPolynomial.X 1)
            (MvPolynomial.isHomogeneous_X R 1) Nat.zero_lt_one := by
    simp only [chart, ← Category.assoc, ← Spec.map_comp]
    congr 2
    exact congrArg CommRingCat.ofHom he.symm
  have ho : Spec.map (CommRingCat.ofHom (translationOverlapFromChart R t)) ≫
      Proj.awayι (grading R) (MvPolynomial.X 1)
        (MvPolynomial.isHomogeneous_X R 1) Nat.zero_lt_one =
      Spec.map (CommRingCat.ofHom (translationOverlapFromChangedChart R t)) ≫
        Proj.awayι (grading R) (translationForm R t)
          (translationForm_homogeneous R t) Nat.zero_lt_one := by
    simp only [translationOverlapFromChart, translationOverlapFromChangedChart,
      Proj.SpecMap_awayMap_awayι]
  rw [← Category.assoc, hs]
  simp only [Category.assoc]
  rw [← Category.assoc (Spec.map (CommRingCat.ofHom (translationOverlapFromChart R t))), ho]
  simp only [Category.assoc]
  rw [show LinearChange.matrixMap R (translationMatrix R t) =
    Proj.map (translationSubstitution R t)
      (LinearChange.linearSubstitution_irrelevant_le R (translationMatrix R t)) from rfl]
  rw [Proj.awayι_comp_map (translationSubstitution R t)
    (LinearChange.linearSubstitution_irrelevant_le R (translationMatrix R t))
    Nat.zero_lt_one (MvPolynomial.X 1) (MvPolynomial.isHomogeneous_X R 1)]
  simp only [chart, ← Category.assoc, ← Spec.map_comp]
  congr 2
  exact congrArg CommRingCat.ofHom (translationOverlapValue_changed R t)

end TranslationOverlap

end AlgebraicGeometry.Scheme.ProjectiveLine.Sections
