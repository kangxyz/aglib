/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Basic
public import Aglib.RingTheory.ScalarHomology.Basic
public import Aglib.RingTheory.Length.ExactSequence
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Additivity of principal Euler expressions

Scalar kernels and cokernels along an exact sequence produce an actual six-term homology
sequence. Under the declared finite-length hypotheses, the associated integer Euler expressions
are additive.

## Extraction basis

Transferred from `R5Lab.RingTheory.LocalLength.PrincipalEulerAdditivity` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`26ee2397a837a665bc1b1c6f248fdacdc0d43009ea147acb68137233d7c5446d`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
namespace Module
universe u v w z
variable {A : Type u} [CommRing A]
variable {U : Type v} {V : Type w} {W : Type z}
variable [AddCommGroup U] [Module A U] [AddCommGroup V] [Module A V]
variable [AddCommGroup W] [Module A W]

/-- Principal Euler length is additive on every short exact sequence for
which the kernel and cokernel lengths are finite. No quotient factor is
assumed free, projective, Cohen--Macaulay, or t-regular. -/
theorem principalEuler_add_of_exact (f : U →ₗ[A] V) (g : V →ₗ[A] W)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) (t : A)
    (hU : FinitePrincipal U t) (hV : FinitePrincipal V t) (hW : FinitePrincipal W t) :
    principalEuler (N := V) t = principalEuler (N := U) t + principalEuler (N := W) t := by
  let δ := principalConnecting f g hf hg hex t
  have h₁ := intLength_exact_pair (scalarKernelMap f t) (scalarKernelMap g t)
    (scalarKernelMap_exact f g hf hex t) hV.1
  have h₂ := intLength_exact_pair (scalarKernelMap g t) δ
    (principalConnecting_exact_right f g hf hg hex t) hW.1
  have h₃ := intLength_exact_pair δ (scalarCokernelMap f t)
    (principalConnecting_exact_left f g hf hg hex t) hU.2
  have h₄ := intLength_exact_pair (scalarCokernelMap f t) (scalarCokernelMap g t)
    (scalarCokernelMap_exact f g hg hex t) hV.2
  have he₁ := LinearEquiv.length_eq (R := A) (M := ScalarKernel U t)
    (N := LinearMap.range (scalarKernelMap f t))
    (LinearEquiv.ofInjective (scalarKernelMap f t) (scalarKernelMap_injective f hf t))
  have hi₁ : intLength (A := A) (LinearMap.range (scalarKernelMap f t)) =
      intLength (A := A) (ScalarKernel U t) :=
    congrArg (fun a : ℕ∞ => (a.toNat : ℤ)) he₁.symm
  let e₄ : LinearMap.range (scalarCokernelMap g t) ≃ₗ[A] ScalarCokernel W t :=
    LinearEquiv.ofBijective (LinearMap.range (scalarCokernelMap g t)).subtype
      ⟨Submodule.subtype_injective _, by
        intro x
        obtain ⟨y, hy⟩ := scalarCokernelMap_surjective g hg t x
        exact ⟨⟨scalarCokernelMap g t y, ⟨y, rfl⟩⟩, hy⟩⟩
  have he₄ := LinearEquiv.length_eq (R := A)
    (M := LinearMap.range (scalarCokernelMap g t)) (N := ScalarCokernel W t) e₄
  have hi₄ : intLength (A := A) (LinearMap.range (scalarCokernelMap g t)) =
      intLength (A := A) (ScalarCokernel W t) :=
    congrArg (fun a : ℕ∞ => (a.toNat : ℤ)) he₄
  rw [hi₁] at h₁
  rw [hi₄] at h₄
  change intLength (A := A) (ScalarCokernel V t) - intLength (A := A) (ScalarKernel V t) =
    (intLength (A := A) (ScalarCokernel U t) - intLength (A := A) (ScalarKernel U t)) +
      (intLength (A := A) (ScalarCokernel W t) - intLength (A := A) (ScalarKernel W t))
  omega

theorem principalEuler_congr (e : U ≃ₗ[A] V) (t : A) :
    principalEuler (N := U) t = principalEuler (N := V) t := by
  have hk := LinearEquiv.length_eq (R := A) (M := ScalarKernel U t) (N := ScalarKernel V t)
    (scalarKernelEquiv e t)
  have hc := LinearEquiv.length_eq (R := A) (M := ScalarCokernel U t) (N := ScalarCokernel V t)
    (scalarCokernelEquiv e t)
  unfold principalEuler
  rw [hk, hc]

theorem finitePrincipal_congr (e : U ≃ₗ[A] V) (t : A) :
    FinitePrincipal U t ↔ FinitePrincipal V t := by
  have hk := LinearEquiv.length_eq (R := A) (M := ScalarKernel U t) (N := ScalarKernel V t)
    (scalarKernelEquiv e t)
  have hc := LinearEquiv.length_eq (R := A) (M := ScalarCokernel U t) (N := ScalarCokernel V t)
    (scalarCokernelEquiv e t)
  unfold FinitePrincipal
  rw [hk, hc]

theorem _root_.Int.integer_telescope (n : ℕ) (a : Fin (n + 1) → ℤ) (b : Fin n → ℤ)
    (hzero : a 0 = 0) (hstep : ∀ i, a i.succ = a i.castSucc + b i) :
    a (Fin.last n) = ∑ i, b i := by
  have h₁ := Fin.sum_univ_succ a
  have h₂ := Fin.sum_univ_castSucc a
  have hb : ∑ i, b i = (∑ i : Fin n, a i.succ) - ∑ i : Fin n, a i.castSucc := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have := hstep i
    omega
  omega

end Module
