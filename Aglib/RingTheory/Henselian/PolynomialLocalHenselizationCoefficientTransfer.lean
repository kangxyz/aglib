/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.HenselizationCoefficientReduction
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationFieldReduction
public import Aglib.RingTheory.MvPolynomial.FiniteSystemReindex

/-! # Removing henselized coefficients at the actual formal point

The original formal map is used, not a newly chosen henselization map.
The same system of finitely many polynomial equations is evaluated in the source
and formal target; the ambient unknown index may be arbitrary.
Its auxiliary coordinates are exactly rigid modulo the maximal ideal.
The final theorem is a conditional transfer of an explicitly supplied polynomial
system solver; it does not assert that such a solver already exists.
-/

@[expose] public section

noncomputable section

open MvPolynomial IsLocalRing

universe u v w

namespace PolynomialLocalHenselization

variable (k : Type u) [Field k] (d : ℕ)

/-- A formal root of a system over the henselization with finitely many equations
extends to a formal root of a system with polynomial coefficients after adjoining
finitely many auxiliary unknowns and equations. The ambient unknown index may be
arbitrary. A source solution at precision `max c 1` recovers the exact original
coefficients and equations. -/
theorem exists_polynomial_coefficient_point_reduction
    {σ : Type v} {ι : Type w} [Finite ι]
    (F : ι → MvPolynomial σ (PolynomialLocalHenselization k d))
    (y : σ → PolynomialLocalRing.FormalSeries k d)
    (hy : ∀ i, eval₂ (toFormalSeries k d).toRingHom y (F i) = 0)
    (c : ℕ) :
    ∃ (a b : ℕ)
      (E : (ι ⊕ Fin b) → MvPolynomial (σ ⊕ Fin a) (MvPolynomial (Fin d) k))
      (z₀ : Fin a → PolynomialLocalHenselization k d),
      (∀ i, eval₂
        (algebraMap (MvPolynomial (Fin d) k) (PolynomialLocalRing.FormalSeries k d))
        (Sum.elim y (fun j => toFormalSeries k d (z₀ j))) (E i) = 0) ∧
      ∀ x : (σ ⊕ Fin a) → PolynomialLocalHenselization k d,
        (∀ i, eval₂
          ((algebraMap (PolynomialLocalRing k d) (PolynomialLocalHenselization k d)).comp
            (algebraMap (MvPolynomial (Fin d) k) (PolynomialLocalRing k d))) x (E i) = 0) →
        (∀ j, toFormalSeries k d (x j) -
          Sum.elim y (fun l => toFormalSeries k d (z₀ l)) j ∈
            maximalIdeal (PolynomialLocalRing.FormalSeries k d) ^ max c 1) →
        (∀ j, x (Sum.inr j) = z₀ j) ∧
        (∀ i, eval₂ (RingHom.id _) (fun j => x (Sum.inl j)) (F i) = 0) ∧
        ∀ j, toFormalSeries k d (x (Sum.inl j)) - y j ∈
          maximalIdeal (PolynomialLocalRing.FormalSeries k d) ^ c := by
  let P := MvPolynomial (Fin d) k
  let L := PolynomialLocalRing k d
  let H := PolynomialLocalHenselization k d
  let C := PolynomialLocalRing.FormalSeries k d
  let τ := (toFormalSeries k d).toRingHom
  let φ : P →+* H := (algebraMap L H).comp (algebraMap P L)
  let : Algebra L C := (PolynomialLocalRing.toFormalSeries k d).toRingHom.toAlgebra
  let τL : H →ₐ[L] C :=
    { τ with
      commutes' := fun r => AlgHom.congr_fun (toFormalSeries_comp_of k d) r }
  have hτL (z : H) : τL z = toFormalSeries k d z := rfl
  have hcomp : τ.comp φ = algebraMap P C :=
    toFormalSeries_comp_polynomial_algebraMap k d
  have hC : (algebraMap L C).comp (algebraMap P L) = algebraMap P C := by
    rw [← hcomp]
    apply RingHom.ext
    intro p
    exact (τL.commutes (algebraMap P L p)).symm
  obtain ⟨a, b, E, z₀, hE⟩ :=
    Henselization.exists_polynomial_system_before_localization.{u, u, v, w, u}
      (A := P) (L := L) (PolynomialLocalRing.originIdeal k d).primeCompl F
  refine ⟨a, b, E, z₀, ?_, ?_⟩
  · have h := (hE C τL y).1.mpr hy
    simpa only [hC, hτL] using h
  · intro x hx hclose
    let z : Fin a → H := fun j => x (Sum.inr j)
    let x₀ : σ → H := fun j => x (Sum.inl j)
    have htuple : Sum.elim x₀ z = x := by
      funext j
      cases j <;> rfl
    have hsource : ∀ i, eval₂ φ (Sum.elim x₀ z) (E i) = 0 := by
      rw [htuple]
      exact hx
    have hres : ∀ j, z j - z₀ j ∈ maximalIdeal H := by
      intro j
      have hformal : toFormalSeries k d (z j - z₀ j) ∈ maximalIdeal C ^ 1 := by
        apply Ideal.pow_le_pow_right (le_max_right c 1)
        simpa only [map_sub, z, Sum.elim_inr] using hclose (Sum.inr j)
      have h := (toFormalSeries_mem_maximalIdeal_pow_iff k d 1 (z j - z₀ j)).mp hformal
      simpa only [pow_one] using h
    have hrig := (hE H (AlgHom.id L H) x₀).2 z hsource hres
    refine ⟨hrig.1, hrig.2, ?_⟩
    intro j
    exact Ideal.pow_le_pow_right (le_max_left c 1) (hclose (Sum.inl j))

/-- An actual solver for all finite polynomial-coefficient systems implies the
full henselized-coefficient solver. The premise is explicit and restricted to
`Fin` indices; the conclusion allows independent finite indices in any universes. -/
theorem exists_solution_of_polynomial_coefficient_solver
    (hsolve : ∀ (s t : ℕ)
      (F : Fin t → MvPolynomial (Fin s) (MvPolynomial (Fin d) k))
      (y : Fin s → PolynomialLocalRing.FormalSeries k d),
      (∀ i, eval₂
        (algebraMap (MvPolynomial (Fin d) k) (PolynomialLocalRing.FormalSeries k d))
        y (F i) = 0) →
      ∀ c : ℕ, ∃ x : Fin s → PolynomialLocalHenselization k d,
        (∀ i, eval₂
          ((algebraMap (PolynomialLocalRing k d) (PolynomialLocalHenselization k d)).comp
            (algebraMap (MvPolynomial (Fin d) k) (PolynomialLocalRing k d))) x (F i) = 0) ∧
        ∀ j, toFormalSeries k d (x j) - y j ∈
          maximalIdeal (PolynomialLocalRing.FormalSeries k d) ^ c)
    {σ : Type v} {ι : Type w} [Finite σ] [Finite ι]
    (F : ι → MvPolynomial σ (PolynomialLocalHenselization k d))
    (y : σ → PolynomialLocalRing.FormalSeries k d)
    (hy : ∀ i, eval₂ (toFormalSeries k d).toRingHom y (F i) = 0)
    (c : ℕ) :
    ∃ x : σ → PolynomialLocalHenselization k d,
      (∀ i, eval₂ (RingHom.id _) x (F i) = 0) ∧
      ∀ j, toFormalSeries k d (x j) - y j ∈
        maximalIdeal (PolynomialLocalRing.FormalSeries k d) ^ c := by
  let P := MvPolynomial (Fin d) k
  let L := PolynomialLocalRing k d
  let H := PolynomialLocalHenselization k d
  let C := PolynomialLocalRing.FormalSeries k d
  let τ := (toFormalSeries k d).toRingHom
  let φ : P →+* H := (algebraMap L H).comp (algebraMap P L)
  have hcomp : τ.comp φ = algebraMap P C :=
    toFormalSeries_comp_polynomial_algebraMap k d
  have hsolve' : ∀ (s t : ℕ) (G : Fin t → MvPolynomial (Fin s) P) (z : Fin s → C),
      (∀ i, eval₂ (τ.comp φ) z (G i) = 0) →
      ∀ N : ℕ, ∃ x : Fin s → H,
        (∀ i, eval₂ φ x (G i) = 0) ∧ ∀ j, τ (x j) - z j ∈ maximalIdeal C ^ N := by
    intro s t G z hz N
    exact hsolve s t G z (by simpa only [hcomp] using hz) N
  obtain ⟨a, b, E, z₀, hformal, hrecover⟩ :=
    exists_polynomial_coefficient_point_reduction k d F y hy c
  let z : (σ ⊕ Fin a) → C := Sum.elim y (fun j => toFormalSeries k d (z₀ j))
  have hz : ∀ i, eval₂ (τ.comp φ) z (E i) = 0 := by
    simpa only [hcomp] using hformal
  obtain ⟨x, hx, hclose⟩ := exists_finite_solution_of_fin_solver
    φ τ (maximalIdeal C) hsolve' E z hz (max c 1)
  have h := hrecover x hx hclose
  exact ⟨fun j => x (Sum.inl j), h.2.1, h.2.2⟩

end PolynomialLocalHenselization
