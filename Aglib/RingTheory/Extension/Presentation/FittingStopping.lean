/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Extension.Presentation.SelectedJacobianStopping
public import Aglib.RingTheory.Extension.Presentation.Fitting

/-!
# Fitting stopping for an actual faithful domain presentation

A nonvanishing Fitting minor selects an actual intermediate quotient. The
selected-open stopping theorem proves smoothness there, and the native smooth
locus localization equality returns to the original prime.
-/

@[expose] public noncomputable section

open MvPolynomial

universe u w

namespace Algebra.Presentation

variable {R B : Type u} {σ : Type w} {ι τ : Type}
variable [CommRing R] [CommRing B] [Algebra R B] [Finite ι]

omit [Finite ι] in
/-- The Jacobian inverted in the actual selected quotient maps to the same
minor of the original relation matrix, with variables as rows. -/
theorem selectedRelationQuotientMap_jacobian [Fintype τ] [DecidableEq τ]
    (P : Presentation R B ι σ) (e : τ → σ) (a : τ → ι)
    (ha : Function.Injective a) :
    P.selectedRelationQuotientMap e (P.selectedRelationPresentation e a ha).jacobian =
      (Matrix.of fun i j => aeval P.val (pderiv (a i) (P.relation (e j)))).det := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  change P.selectedRelationQuotientMap e (Ideal.Quotient.mk _
    (P.selectedRelationPresentation e a ha).jacobiMatrix.det) = _
  rw [P.selectedRelationQuotientMap_mk, AlgHom.map_det]
  congr 1
  ext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, selectedRelationPresentation,
    PreSubmersivePresentation.jacobiMatrix_naive, Function.comp_apply, Matrix.of_apply]

variable [IsDomain R] [IsRegularRing R] [IsDomain B] [FaithfulSMul R B]

/-- For the actual faithful domain presentation, a nonvanishing Fitting ideal
at the original prime supplies smoothness, without a fibre-dimension premise. -/
theorem isSmoothAt_of_fittingIdeal_kaehler_not_le
    (P : Presentation R B ι σ) (r : ℕ)
    (hdeg : Algebra.trdeg R B = (r : Cardinal))
    (q : Ideal B) [q.IsPrime]
    (hfit : ¬ Module.fittingIdeal B (KaehlerDifferential R B) r ≤ q) :
    Algebra.IsSmoothAt R q := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hcard : (r : Cardinal) ≤ (Nat.card ι : Cardinal) := by
    rw [← hdeg]
    simpa [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype,
      Nat.card_eq_fintype_card] using
      trdeg_le_of_surjective (aeval P.val) P.aeval_val_surjective
  have hr : r ≤ Nat.card ι := by exact_mod_cast hcard
  let c := Nat.card ι - r
  let M : Matrix ι σ B := Matrix.of fun i j => aeval P.val (pderiv i (P.relation j))
  have hex : ∃ (a : Fin c → ι) (e : Fin c → σ), (M.submatrix a e).det ∉ q := by
    by_contra! h
    apply hfit
    rw [P.fittingIdeal_kaehler_eq_minorIdeal, Matrix.minorIdeal, Ideal.span_le]
    rintro _ ⟨a, e, rfl⟩
    exact h a e
  obtain ⟨a, e, hminor⟩ := hex
  have ha : Function.Injective a := by
    intro i j hij
    by_contra hne
    apply hminor
    rw [Matrix.det_zero_of_row_eq hne (by
      ext k
      simp only [Matrix.submatrix_apply, hij])]
    exact q.zero_mem
  let δ := P.selectedRelationQuotientMap e (P.selectedRelationPresentation e a ha).jacobian
  have hδ : δ ∉ q := by
    simpa only [δ, P.selectedRelationQuotientMap_jacobian, M, Matrix.submatrix,
      Matrix.of_apply] using hminor
  let E := P.SelectedJacobianTarget e a ha
  let q' : Ideal E := q.map (algebraMap B E)
  have hdisj : Disjoint (Submonoid.powers δ : Set B) (q : Set B) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime δ).mpr hδ
  let : q'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers δ) E q inferInstance hdisj
  have hq : q'.under B = q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers δ) E inferInstance hdisj
  have hselected : Algebra.IsSmoothAt R q' :=
    P.isSmoothAt_selectedJacobianTarget e a ha
      (by simpa only [Nat.card_fin, c, Nat.sub_sub_self hr] using hdeg) q'
  have hmem : (⟨q', inferInstance⟩ : PrimeSpectrum E) ∈ Algebra.smoothLocus R E := hselected
  rw [← Algebra.smoothLocus_comap_of_isLocalization (R := R) (A := B) δ] at hmem
  change Algebra.IsSmoothAt R (q'.under B) at hmem
  simpa only [hq] using hmem

end Algebra.Presentation
