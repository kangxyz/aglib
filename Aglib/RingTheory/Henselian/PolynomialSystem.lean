/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Etale.PolynomialSystemChart
public import Aglib.RingTheory.Henselian.EtaleQuotientLifting

/-!
# Lifting nonsingular polynomial solutions over a Henselian local ring

A finite square system with a nonsingular approximate solution modulo an arbitrary
proper ideal has a genuine solution with the same residue coordinates. The proof
uses the actual Jacobian-localized equation quotient and étale quotient lifting.
-/

@[expose] public section

universe u v

open MvPolynomial

namespace HenselianLocalRing

variable {R : Type u} {σ : Type v} [CommRing R] [HenselianLocalRing R]
variable [Fintype σ] [DecidableEq σ]

/-- A nonsingular solution modulo any proper ideal of a Henselian local ring lifts
without changing its residue coordinates. -/
theorem exists_eval_eq_zero_mod_ideal_of_isUnit_det
    (F : σ → MvPolynomial σ R) (y0 : σ → R) (I : Ideal R) (hI : I ≠ ⊤)
    (hF : ∀ i, eval y0 (F i) ∈ I)
    (hJ : IsUnit (Matrix.det (Matrix.of fun i j ↦ eval y0 (pderiv j (F i))))) :
    ∃ y : σ → R, (∀ i, eval y (F i) = 0) ∧ ∀ i, y i - y0 i ∈ I := by
  let π := Ideal.Quotient.mkₐ R I
  let x : σ → R ⧸ I := fun i ↦ π (y0 i)
  have heval (p : MvPolynomial σ R) : aeval x p = π (eval y0 p) := by
    simpa only [x, MvPolynomial.aeval_eq_eval] using
      (MvPolynomial.comp_aeval_apply y0 π p).symm
  have hx : ∀ i, aeval x (F i) = 0 := by
    intro i
    rw [heval]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hF i)
  have hdet : eval y0
      (Matrix.det (Matrix.of fun i j ↦ pderiv j (F i))) =
      (Matrix.det (Matrix.of fun i j ↦ eval y0 (pderiv j (F i)))) := by
    rw [RingHom.map_det]
    rfl
  have hD : IsUnit (aeval x
      (Matrix.det (Matrix.of fun i j ↦ pderiv j (F i)))) := by
    rw [heval, hdet]
    exact hJ.map π
  let pnt := systemEtaleChartPoint F x hx hD
  obtain ⟨g, hg⟩ := (quotient_comp_bijective_of_etale R (SystemEtaleChart F) I hI).2 pnt
  let y : σ → R := fun i ↦ g (systemEtaleChartMap F (X i))
  have hy (p : MvPolynomial σ R) : eval y p = g (systemEtaleChartMap F p) := by
    exact (AlgHom.congr_fun (comp_systemEtaleChartMap_eq_aeval F g) p).symm
  refine ⟨y, ?_, ?_⟩
  · intro i
    rw [hy, systemEtaleChartMap_relation, map_zero]
  · intro i
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hcoord := AlgHom.congr_fun hg (systemEtaleChartMap F (X i))
    change π (y i - y0 i) = 0
    rw [map_sub]
    have hcoord' : π (y i) = π (y0 i) := by
      simpa only [AlgHom.comp_apply, pnt, systemEtaleChartPoint_coordinate, y, x] using hcoord
    rw [hcoord', sub_self]

end HenselianLocalRing
