/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.FiniteEtale.TorsorExtension
public import Mathlib.RingTheory.Invariant.Basic

/-!
# Coefficient points of an algebraic torsor

The inverse of the actual transporter gives the coefficient carrying one supplied
point to another. This gives all-point fixedness from coefficient fixedness and
one fixed point. The transporter bijectivity and actual points remain inputs.

Extraction source: `R5Lab.Aglib.AlgebraicGeometry.Normalization.TorsorInertia`,
lines 45–161, at R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`,
SHA-256 `12e18060a2b4ecaca205823a13eea92abd77d3f21e709a462f428a64e5fd3b0d`.
-/

@[expose] public section

noncomputable section
open scoped TensorProduct
namespace Algebra.FiniteEtale.TorsorExtension
open Algebra.FiniteEtale.GenericMaps

universe u

section GenericFibre

variable (K Ω A C : Type u) [CommRing K] [CommRing Ω] [Algebra K Ω]
  [CommRing A] [Algebra K A] [CommRing C] [Algebra K C]

/-- If the actual transporter is bijective, every pair of torsor points has
a coefficient point taking the first to the second. The argument uses the
inverse of the actual algebra transporter, not a trivialization of A.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C4: coefficient-point transitivity from a bijective transporter over
arbitrary commutative base/coefficient algebras. -/
theorem exists_coefficient_point
    (δ : A →ₐ[K] A ⊗[K] C)
    (hδ : Function.Bijective (transporter K A C δ))
    (f g : A →ₐ[K] Ω) :
    ∃ h : C →ₐ[K] Ω,
      (Algebra.TensorProduct.lift f h (fun _ _ => .all _ _)).comp δ = g := by
  let θ := AlgEquiv.ofBijective (transporter K A C δ) hδ
  let ψ : (A ⊗[K] A) →ₐ[K] Ω :=
    Algebra.TensorProduct.lift f g (fun _ _ => .all _ _)
  let φ : (A ⊗[K] C) →ₐ[K] Ω := ψ.comp θ.symm.toAlgHom
  have hleft : φ.comp Algebra.TensorProduct.includeLeft = f := by
    apply AlgHom.ext
    intro a
    have ht : transporter K A C δ (a ⊗ₜ[K] (1 : A)) = a ⊗ₜ[K] (1 : C) := by
      simp [transporter]
    have hi : θ.symm (a ⊗ₜ[K] (1 : C)) = a ⊗ₜ[K] (1 : A) := by
      apply θ.injective
      simpa only [AlgEquiv.apply_symm_apply, θ, AlgEquiv.ofBijective_apply] using ht.symm
    simp [φ, ψ, hi]
  let h : C →ₐ[K] Ω := φ.comp Algebra.TensorProduct.includeRight
  have hφ : Algebra.TensorProduct.lift f h (fun _ _ => .all _ _) = φ := by
    apply Algebra.TensorProduct.ext
    · simp only [Algebra.TensorProduct.lift_comp_includeLeft]
      exact hleft.symm
    · simp only [Algebra.TensorProduct.lift_comp_includeRight]
      rfl
  refine ⟨h, ?_⟩
  rw [hφ]
  apply AlgHom.ext
  intro a
  have ht : transporter K A C δ ((1 : A) ⊗ₜ[K] a) = δ a := by
    simp [transporter, ← Algebra.TensorProduct.one_def]
  have hi : θ.symm (δ a) = (1 : A) ⊗ₜ[K] a := by
    apply θ.injective
    simpa only [AlgEquiv.apply_symm_apply, θ, AlgEquiv.ofBijective_apply] using ht.symm
  simp [φ, ψ, hi]

/-- A coefficient-fibre automorphism fixing one geometric torsor point fixes
every geometric torsor point. No rational point is assumed or constructed.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C4: a bijective transporter and an Omega-automorphism fixing every
coefficient point and one A-point give all-A-point fixedness. -/
theorem geometric_fibre_fixed_of_one_point
    (δ : A →ₐ[K] A ⊗[K] C)
    (hδ : Function.Bijective (transporter K A C δ))
    (σ : Ω ≃ₐ[K] Ω)
    (hC : ∀ h : C →ₐ[K] Ω, σ.toAlgHom.comp h = h)
    (f : A →ₐ[K] Ω) (hf : σ.toAlgHom.comp f = f) :
    ∀ g : A →ₐ[K] Ω, σ.toAlgHom.comp g = g := by
  intro g
  obtain ⟨h, hg⟩ := exists_coefficient_point K Ω A C δ hδ f g
  rw [← hg]
  have ht : σ.toAlgHom.comp
      (Algebra.TensorProduct.lift f h (fun _ _ => .all _ _)) =
        Algebra.TensorProduct.lift f h (fun _ _ => .all _ _) := by
    apply Algebra.TensorProduct.ext'
    intro a c
    have hf' := DFunLike.congr_fun hf a
    have hh' := DFunLike.congr_fun (hC h) c
    simpa using congrArg₂ (fun x y : Ω => x * y) hf' hh'
  rw [← AlgHom.comp_assoc, ht]

end GenericFibre

section CoefficientInertia

variable (R K Ω A H : Type u) [CommRing R]
  [Field K] [Algebra R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [CommRing H] [Algebra R H]
variable {ε : H →ₐ[R] R} {Δ : H →ₐ[R] H ⊗[R] H}
variable (Q : Ideal (integralClosure R Ω))

/-- Trivial inertia on the actual generic coefficient fibre and one common
inertia-fixed geometric torsor point yield the full inertia premise consumed
by the tracked reverse normalization theorem.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded subset C5: the actual H_K coefficient premise and one common inertia-fixed
geometric point give all-embeddings inertia; no DVR or prime-Q premise is used in this
bridge. -/
theorem inertia_trivial_of_fixed_point
    (τ : OriginalTorsorData R K A H ε Δ)
    (hH : ∀ σ ∈ Q.inertia (Ω ≃ₐ[K] Ω), ∀ h : (K ⊗[R] H) →ₐ[K] Ω,
      σ.toAlgHom.comp h = h)
    (f : A →ₐ[K] Ω)
    (hf : ∀ σ ∈ Q.inertia (Ω ≃ₐ[K] Ω), σ.toAlgHom.comp f = f) :
    ∀ σ ∈ Q.inertia (Ω ≃ₐ[K] Ω), ∀ g : A →ₐ[K] Ω,
      σ.toAlgHom.comp g = g := by
  intro σ hσ
  exact geometric_fibre_fixed_of_one_point K Ω A (K ⊗[R] H)
    τ.coaction.coact τ.transporter_bijective σ (hH σ hσ) f (hf σ hσ)

end CoefficientInertia


end Algebra.FiniteEtale.TorsorExtension
