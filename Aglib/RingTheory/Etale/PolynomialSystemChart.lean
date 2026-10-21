/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The étale chart of a square polynomial system

The quotient by a finite square system becomes étale after inverting the native
presentation Jacobian. Its points are actual algebra homomorphisms, with the
images of the original polynomial coordinates retained explicitly.
-/

@[expose] public section

universe u v w

open MvPolynomial

namespace Algebra.PreSubmersivePresentation

variable {R : Type u} {S : Type v} {σ : Type w}
variable [CommRing R] [CommRing S] [Algebra R S] [Finite σ]

/-- Inverting the Jacobian turns a square presentation into a submersive presentation. -/
noncomputable def submersivePresentationAwayJacobian
    (P : PreSubmersivePresentation R S σ σ) :
    SubmersivePresentation R (Localization.Away P.jacobian) (Unit ⊕ σ) (Unit ⊕ σ) where
  __ := (localizationAway (Localization.Away P.jacobian) P.jacobian).comp P
  jacobian_isUnit := by
    rw [comp_jacobian_eq_jacobian_smul_jacobian, localizationAway_jacobian,
      Algebra.smul_def]
    have h : IsUnit (algebraMap S (Localization.Away P.jacobian) P.jacobian) :=
      IsLocalization.map_units _ (⟨P.jacobian, 1, by simp⟩ : Submonoid.powers P.jacobian)
    exact h.mul h

/-- The localization of a square presentation at its Jacobian is étale. -/
theorem etale_away_jacobian (P : PreSubmersivePresentation R S σ σ) :
    Etale R (Localization.Away P.jacobian) := by
  let : IsStandardSmoothOfRelativeDimension 0 R (Localization.Away P.jacobian) :=
    P.submersivePresentationAwayJacobian.isStandardSmoothOfRelativeDimension
      (by simp [Presentation.dimension])
  infer_instance

end Algebra.PreSubmersivePresentation

namespace MvPolynomial

variable {R : Type u} {σ : Type v} [CommRing R]
variable (F : σ → MvPolynomial σ R)

/-- The native square presentation of the quotient by a polynomial system. -/
noncomputable abbrev systemPresentation :
    Algebra.PreSubmersivePresentation R (MvPolynomial σ R ⧸ Ideal.span (Set.range F)) σ σ :=
  Algebra.PreSubmersivePresentation.naive (v := F) id Function.injective_id

variable [Finite σ]

/-- The polynomial-system chart is the localization of the actual equation quotient. -/
abbrev SystemEtaleChart := Localization.Away (systemPresentation F).jacobian

noncomputable instance : Algebra.Etale R (SystemEtaleChart F) :=
  (systemPresentation F).etale_away_jacobian

/-- The canonical coordinate homomorphism into the chart. -/
noncomputable def systemEtaleChartMap : MvPolynomial σ R →ₐ[R] SystemEtaleChart F :=
  (IsScalarTower.toAlgHom R (MvPolynomial σ R ⧸ Ideal.span (Set.range F))
    (SystemEtaleChart F)).comp (Ideal.Quotient.mkₐ R (Ideal.span (Set.range F)))

@[simp]
theorem systemEtaleChartMap_relation (i : σ) : systemEtaleChartMap F (F i) = 0 := by
  have h : Ideal.Quotient.mk (Ideal.span (Set.range F)) (F i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
  change algebraMap _ (SystemEtaleChart F)
    (Ideal.Quotient.mk (Ideal.span (Set.range F)) (F i)) = 0
  rw [h, map_zero]

theorem systemEtaleChartMap_C (r : R) :
    systemEtaleChartMap F (C r) = algebraMap R (SystemEtaleChart F) r :=
  (systemEtaleChartMap F).commutes r

/-- Reading the original coordinates of a chart point recovers its polynomial evaluation. -/
theorem comp_systemEtaleChartMap_eq_aeval {B : Type w} [CommRing B] [Algebra R B]
    (g : SystemEtaleChart F →ₐ[R] B) :
    g.comp (systemEtaleChartMap F) =
      aeval (fun i ↦ g (systemEtaleChartMap F (X i))) :=
  MvPolynomial.aeval_unique _

section Matrix

variable [Fintype σ] [DecidableEq σ]

omit [Finite σ] in
/-- Native presentation matrices use variables as rows, whereas the displayed matrix
uses equations as rows. This is an actual transpose comparison. -/
theorem systemPresentation_jacobiMatrix :
    (systemPresentation F).jacobiMatrix =
      (Matrix.transpose (Matrix.of fun i j ↦ pderiv j (F i))) := by
  ext i j
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  rfl

/-- The native Jacobian is the quotient image of the usual equation-row determinant. -/
theorem systemPresentation_jacobian :
    (systemPresentation F).jacobian =
      Ideal.Quotient.mk (Ideal.span (Set.range F))
        (Matrix.det (Matrix.of fun i j ↦ pderiv j (F i))) := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    systemPresentation_jacobiMatrix, Matrix.det_transpose]
  rfl

variable {B : Type w} [CommRing B] [Algebra R B]
variable (x : σ → B) (hF : ∀ i, aeval x (F i) = 0)

/-- Evaluation at a solution descends to the actual equation quotient. -/
noncomputable def systemQuotientPoint :
    (MvPolynomial σ R ⧸ Ideal.span (Set.range F)) →ₐ[R] B :=
  Ideal.Quotient.liftₐ _ (aeval x) (by
    intro p hp
    have hker : Ideal.span (Set.range F) ≤ RingHom.ker (aeval x).toRingHom := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hF i
    exact hker hp)

omit [Finite σ] [Fintype σ] [DecidableEq σ] in
@[simp]
theorem systemQuotientPoint_mk (p : MvPolynomial σ R) :
    systemQuotientPoint F x hF (Ideal.Quotient.mk (Ideal.span (Set.range F)) p) =
      aeval x p := rfl

/-- A solution with invertible determinant gives a point of the genuine étale chart. -/
noncomputable def systemEtaleChartPoint
    (hD : IsUnit (aeval x
      (Matrix.det (Matrix.of fun i j ↦ pderiv j (F i))))) :
    SystemEtaleChart F →ₐ[R] B :=
  IsLocalization.Away.liftAlgHom (systemPresentation F).jacobian
    (f := systemQuotientPoint F x hF) (by
      rw [systemPresentation_jacobian, systemQuotientPoint_mk]
      exact hD)

@[simp]
theorem systemEtaleChartPoint_map
    (hD : IsUnit (aeval x
      (Matrix.det (Matrix.of fun i j ↦ pderiv j (F i)))))
    (p : MvPolynomial σ R) :
    systemEtaleChartPoint F x hF hD (systemEtaleChartMap F p) = aeval x p := by
  have h : IsUnit (systemQuotientPoint F x hF (systemPresentation F).jacobian) := by
    rw [systemPresentation_jacobian, systemQuotientPoint_mk]
    exact hD
  change IsLocalization.Away.lift (systemPresentation F).jacobian h
    (algebraMap _ (SystemEtaleChart F)
      (Ideal.Quotient.mk (Ideal.span (Set.range F)) p)) = _
  rw [IsLocalization.Away.lift_eq]
  exact systemQuotientPoint_mk F x hF p

theorem systemEtaleChartPoint_coordinate
    (hD : IsUnit (aeval x
      (Matrix.det (Matrix.of fun i j ↦ pderiv j (F i))))) (i : σ) :
    systemEtaleChartPoint F x hF hD (systemEtaleChartMap F (X i)) = x i := by
  simp

end Matrix
end MvPolynomial
