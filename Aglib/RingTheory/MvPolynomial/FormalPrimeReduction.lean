/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPolynomial.PrimeJacobianReduction
public import Aglib.RingTheory.MvPolynomial.AdicEquationsRecovery

/-!
# Generic reduction at the actual formal evaluation kernel

The auxiliary relations are chosen from a finite generating family of the
actual prime kernel of the given formal point. The original equations need
not generate that prime. Their recovery is proved at a sufficiently precise
source solution of the selected equations, using one multiplier nonzero at
the formal point and cancellation only in the target domain.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {A B C σ ι : Type*} [CommRing A] [IsNoetherianRing A]
  [CommRing B] [CommRing C] [IsDomain C] [Finite σ]

local instance (f : A →+* C) (y : σ → C) :
    (RingHom.ker (eval₂Hom f y)).IsPrime := RingHom.ker_isPrime _

/-- Reduce original equations to selected equations with a nonvanishing
Jacobian minor at the same formal point. Formal smoothness is required only
of the actual generic residue field, and remains a separate geometric input. -/
theorem exists_selected_system_at_formal_prime
    (I : Ideal C) [IsHausdorff I C]
    (φ : A →+* B) (τ : B →+* C) (hτ : Function.Injective τ)
    (F : ι → MvPolynomial σ A) (y : σ → C)
    (hy : ∀ i, eval₂ (τ.comp φ) y (F i) = 0)
    [Algebra.FormallySmooth A (RingHom.ker (eval₂Hom (τ.comp φ) y)).ResidueField]
    (c : ℕ) :
    ∃ (r : ℕ) (G : Fin r → MvPolynomial σ A) (cols : Fin r ↪ σ) (N : ℕ),
      c ≤ N ∧ (∀ j, eval₂ (τ.comp φ) y (G j) = 0) ∧
      eval₂ (τ.comp φ) y
        (Matrix.det (Matrix.of fun i j => pderiv (cols j) (G i))) ≠ 0 ∧
      ∀ x : σ → B, (∀ j, τ (x j) - y j ∈ I ^ N) →
        (∀ j, eval₂ φ x (G j) = 0) → ∀ i, eval₂ φ x (F i) = 0 := by
  classical
  let q := RingHom.ker (eval₂Hom (τ.comp φ) y)
  let : q.IsPrime := RingHom.ker_isPrime _
  obtain ⟨m, H, hH⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian q)
  obtain ⟨r, rows, cols, h, hh, hδ, hmul⟩ :=
    exists_selected_jacobian_minor_and_multiplier q H hH
  let G : Fin r → MvPolynomial σ A := fun i => H (rows i)
  have hmem : ∀ i, h * F i ∈ Ideal.span (Set.range G) := fun i =>
    hmul (F i) (RingHom.mem_ker.mpr (hy i))
  have hnonzero : eval₂ (τ.comp φ) y h ≠ 0 := by
    exact fun hz => hh (RingHom.mem_ker.mpr hz)
  obtain ⟨N, hc, hN⟩ := exists_precision_recover_equations I φ τ hτ G F h hmem y hnonzero c
  refine ⟨r, G, cols, N, hc, ?_, ?_, hN⟩
  · intro j
    change (eval₂Hom (τ.comp φ) y) (G j) = 0
    apply RingHom.mem_ker.mp
    change G j ∈ q
    rw [← hH]
    exact Ideal.subset_span ⟨rows j, rfl⟩
  · exact fun hz => hδ (RingHom.mem_ker.mpr hz)

end MvPolynomial
