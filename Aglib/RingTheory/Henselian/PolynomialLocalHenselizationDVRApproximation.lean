/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationDVRReduction
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationSelectedStep
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationZeroSelected
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationCoefficientTransfer

/-!
# Formal-series approximation under the intrinsic DVR condition

The induction hypothesis solves every finite system over the actual lower
polynomial-origin henselization. In every dimension, including zero, the actual
global smooth-centre reduction first supplies an enlarged selected system with
a coefficient-residue-nonzero determinant. The existing selected-system solvers
then give a close exact root, and restriction to the literal left coordinates
recovers the original equations. Henselized coefficients are removed by the
existing coefficient-transfer theorem at each induction stage.

The coefficient maps and the formal point are the original ones throughout.
This is the maximal-adic formal-series endpoint only: transfer to arbitrary
proper-ideal completions and to outer finite-type local models is separate.
No geometric reduction, strict modification step, or approximation solver is
assumed in either final statement. The explicit coefficient premise is only
geometric reducedness of the actual completed fraction field under its
canonical action.
-/

@[expose] public noncomputable section

namespace PolynomialLocalHenselization

open MvPolynomial IsLocalRing

universe u v w

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Full finite-system approximation under the intrinsic DVR condition, with
arbitrary coefficients in the actual polynomial-origin henselization. The
induction includes the zero-variable selected-system argument at its first
consumer and retains all requested maximal-adic precision. -/
theorem exists_solution_approximation_fin_of_geometricallyReducedFractionCompletion (n : ℕ)
    (hcoeff : AdicCompletion.HasGeometricallyReducedFractionCompletion R) :
    ∀ (s t : ℕ) (F : Fin t → MvPolynomial (Fin s) (PolynomialLocalHenselization R n))
      (y : Fin s → PolynomialLocalRing.FormalSeries R n),
      (∀ i, eval₂ (toFormalSeries R n).toRingHom y (F i) = 0) →
      ∀ c : ℕ, ∃ x : Fin s → PolynomialLocalHenselization R n,
        (∀ i, eval x (F i) = 0) ∧
        ∀ j, toFormalSeries R n (x j) - y j ∈
          maximalIdeal (PolynomialLocalRing.FormalSeries R n) ^ c := by
  classical
  -- This is only the combination of the two existing coefficient squares.
  have hformal (d : ℕ) :
      algebraMap (MvPolynomial (Fin d) R) (PolynomialLocalRing.FormalSeries R d) =
        (PolynomialLocalRing.polynomialToFormalSeries R d).toRingHom := by
    apply RingHom.ext
    intro p
    exact (RingHom.congr_fun (toFormalSeries_comp_polynomial_algebraMap R d) p).symm.trans
      (toFormalSeries_polynomialToHenselization R d p)
  induction n with
  | zero =>
      intro s t F y hy c
      apply exists_solution_of_polynomial_coefficient_solver R 0 ?_ F y hy c
      intro s t E b hE c
      have hE' : ∀ i, eval₂
          (PolynomialLocalRing.polynomialToFormalSeries R 0).toRingHom b (E i) = 0 := by
        simpa only [hformal 0] using hE
      obtain ⟨ℓ, z, r, G, cols, N, hleft, hc, hG, hdet, hrecover⟩ :=
        exists_selected_system_at_formal_point_of_geometricallyReducedFractionCompletion
          R 0 hcoeff s t E b hE' c
      let ψ := (polynomialToHenselization R 0).toRingHom
      let τ := (toFormalSeries R 0).toRingHom
      let G₀ : Fin r → MvPolynomial (Fin s ⊕ Fin ℓ) (PolynomialLocalHenselization R 0) :=
        fun i => MvPolynomial.map ψ (G i)
      have hcomp : τ.comp ψ =
          (PolynomialLocalRing.polynomialToFormalSeries R 0).toRingHom :=
        (toFormalSeries_comp_polynomial_algebraMap R 0).trans (hformal 0)
      have hG₀ : ∀ i, eval₂ τ z (G₀ i) = 0 := by
        intro i
        simpa only [G₀, eval₂_map, hcomp] using hG i
      have hdetMap :
          Matrix.det (Matrix.of fun i j => pderiv (cols j) (G₀ i)) =
            MvPolynomial.map ψ
              (Matrix.det (Matrix.of fun i j => pderiv (cols j) (G i))) := by
        rw [RingHom.map_det]
        congr 1
        apply Matrix.ext
        intro i j
        change pderiv (cols j) (MvPolynomial.map ψ (G i)) =
          MvPolynomial.map ψ (pderiv (cols j) (G i))
        exact pderiv_map (φ := ψ) (f := G i) (i := cols j)
      have hdet₀ : MvPowerSeries.map (residue (AdicCompletion (maximalIdeal R) R))
          (eval₂ τ z (Matrix.det (Matrix.of fun i j => pderiv (cols j) (G₀ i)))) ≠ 0 := by
        rw [hdetMap, eval₂_map, hcomp]
        exact hdet
      obtain ⟨x, hx, hclose⟩ :=
        exists_zero_of_selected_system_zero_of_residue_ne_zero R cols G₀ z hG₀ hdet₀ N
      have hxG : ∀ i, eval₂ (polynomialToHenselization R 0).toRingHom x (G i) = 0 := by
        intro i
        simpa only [G₀, eval_map] using hx i
      refine ⟨fun j => x (Sum.inl j), hrecover x hclose hxG, ?_⟩
      intro j
      have h := Ideal.pow_le_pow_right hc (hclose (Sum.inl j))
      simpa only [hleft] using h
  | succ n ih =>
      intro s t F y hy c
      apply exists_solution_of_polynomial_coefficient_solver R (n + 1) ?_ F y hy c
      intro s t E b hE c
      have hE' : ∀ i, eval₂
          (PolynomialLocalRing.polynomialToFormalSeries R (n + 1)).toRingHom b (E i) = 0 := by
        simpa only [hformal (n + 1)] using hE
      obtain ⟨ℓ, z, r, G, cols, N, hleft, hc, hG, hdet, hrecover⟩ :=
        exists_selected_system_at_formal_point_of_geometricallyReducedFractionCompletion
          R (n + 1) hcoeff s t E b hE' c
      obtain ⟨x, hx, hclose⟩ :=
        exists_zero_of_selected_polynomial_system_of_residue_ne_zero R n ih
          cols G z hG hdet N
      refine ⟨fun j => x (Sum.inl j), hrecover x hclose hx, ?_⟩
      intro j
      have h := Ideal.pow_le_pow_right hc (hclose (Sum.inl j))
      simpa only [hleft] using h

/-- Every formal root of a finite system over the actual polynomial-origin
henselization under the intrinsic DVR condition has an exact source root at any
prescribed maximal-adic precision. Equation and unknown indices may lie in
independent universes; only native finite reindexing is used. -/
theorem exists_solution_approximation_of_geometricallyReducedFractionCompletion (n : ℕ)
    (hcoeff : AdicCompletion.HasGeometricallyReducedFractionCompletion R)
    {σ : Type v} {ι : Type w} [Finite σ] [Finite ι]
    (F : ι → MvPolynomial σ (PolynomialLocalHenselization R n))
    (y : σ → PolynomialLocalRing.FormalSeries R n)
    (hy : ∀ i, eval₂ (toFormalSeries R n).toRingHom y (F i) = 0) (c : ℕ) :
    ∃ x : σ → PolynomialLocalHenselization R n,
      (∀ i, eval x (F i) = 0) ∧
      ∀ j, toFormalSeries R n (x j) - y j ∈
        maximalIdeal (PolynomialLocalRing.FormalSeries R n) ^ c := by
  apply exists_finite_solution_of_fin_solver (RingHom.id (PolynomialLocalHenselization R n))
    (toFormalSeries R n).toRingHom
    (maximalIdeal (PolynomialLocalRing.FormalSeries R n)) ?_ F y ?_ c
  · intro s t E b hE c
    exact exists_solution_approximation_fin_of_geometricallyReducedFractionCompletion
      R n hcoeff s t E b
      (by simpa only [RingHom.comp_id] using hE) c
  · simpa only [RingHom.comp_id] using hy

end PolynomialLocalHenselization
