/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPolynomial.SmoothCentreJacobianReduction
public import Aglib.RingTheory.MvPolynomial.AdicEquationsRecovery

/-!
# Selected equations at the actual formal point's smooth centre

The minor avoids a specified prime of the formal target, not only zero.
Smoothness is imposed at the inverse-image prime in the actual formal
kernel quotient. The residue field itself need not be smooth.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {A B C σ ι : Type*} [CommRing A] [IsNoetherianRing A]
  [CommRing B] [CommRing C] [IsDomain C] [Finite σ]

local instance (f : A →+* C) (y : σ → C) :
    (RingHom.ker (eval₂Hom f y)).IsPrime := RingHom.ker_isPrime _

/-- A smooth actual centre supplies a minor nonzero in the specified
residue domain and selected equations recovering all original equations. -/
theorem exists_selected_system_at_smooth_formal_centre
    (I : Ideal C) [IsHausdorff I C]
    (φ : A →+* B) (τ : B →+* C) (hτ : Function.Injective τ)
    (F : ι → MvPolynomial σ A) (y : σ → C)
    (hy : ∀ i, eval₂ (τ.comp φ) y (F i) = 0)
    (p : Ideal C) [p.IsPrime]
    [Algebra.IsSmoothAt A (p.comap (eval₂Hom (τ.comp φ) y).kerLift)]
    (c : ℕ) :
    ∃ (r : ℕ) (G : Fin r → MvPolynomial σ A) (cols : Fin r ↪ σ) (N : ℕ),
      c ≤ N ∧ (∀ j, eval₂ (τ.comp φ) y (G j) = 0) ∧
      eval₂ (τ.comp φ) y
        (Matrix.det (Matrix.of fun i j => pderiv (cols j) (G i))) ∉ p ∧
      ∀ x : σ → B, (∀ j, τ (x j) - y j ∈ I ^ N) →
        (∀ j, eval₂ φ x (G j) = 0) → ∀ i, eval₂ φ x (F i) = 0 := by
  classical
  let q := RingHom.ker (eval₂Hom (τ.comp φ) y)
  let : q.IsPrime := RingHom.ker_isPrime _
  obtain ⟨m, H, hH⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian q)
  obtain ⟨r, rows, cols, h, hh, hδ, hmul⟩ :=
    exists_selected_jacobian_minor_and_multiplier_at_smooth_centre q
      (p.comap (eval₂Hom (τ.comp φ) y).kerLift) H hH
  let G : Fin r → MvPolynomial σ A := fun i => H (rows i)
  have hmem : ∀ i, h * F i ∈ Ideal.span (Set.range G) := fun i =>
    hmul (F i) (RingHom.mem_ker.mpr (hy i))
  have hhvalue : eval₂ (τ.comp φ) y h ∉ p := by
    change eval₂ (τ.comp φ) y h ∉ p at hh
    exact hh
  have hnonzero : eval₂ (τ.comp φ) y h ≠ 0 := by
    intro hz
    apply hhvalue
    rw [hz]
    exact p.zero_mem
  obtain ⟨N, hc, hN⟩ := exists_precision_recover_equations I φ τ hτ G F h hmem y hnonzero c
  refine ⟨r, G, cols, N, hc, ?_, ?_, hN⟩
  · intro j
    change (eval₂Hom (τ.comp φ) y) (G j) = 0
    apply RingHom.mem_ker.mp
    change G j ∈ q
    rw [← hH]
    exact Ideal.subset_span ⟨rows j, rfl⟩
  · change eval₂ (τ.comp φ) y
      (Matrix.det (Matrix.of fun i j => pderiv (cols j) (G i))) ∉ p at hδ
    exact hδ

end MvPolynomial
