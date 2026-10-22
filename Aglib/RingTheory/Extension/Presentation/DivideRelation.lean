/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPolynomial.LocalConstantDivisibility
public import Mathlib.RingTheory.Extension.Generators
public import Mathlib.Algebra.Regular.Basic

/-! # Dividing an actual relation a second time

A point over a local target forces divisibility of the remaining constant coefficient.
The polynomial quotient is then explicitly constructed, and its membership in the actual
relation kernel follows by cancellation in the presented algebra.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace Algebra.Generators

variable {R M S ι : Type*} [CommRing R] [CommRing M] [CommRing S]
variable [Algebra R M] [Algebra R S] [IsLocalRing R] [IsLocalRing S] [Fintype ι]

set_option backward.isDefEq.respectTransparency false in
/-- A genuine relation with divisible linear and nonlinear coefficients admits a genuine
polynomial quotient when it has a local point and the scale is regular in the algebra. -/
theorem exists_divided_relation_of_local_point (G : Generators R M ι) (χ : M →ₐ[R] S)
    [IsLocalHom (algebraMap R S)] (p c : R) (a : ι → R)
    (f Q : MvPolynomial ι R) (hf : f ∈ G.ker)
    (hp : IsLocalRing.maximalIdeal R = Ideal.span {p})
    (ha : ∀ i, p ∣ a i)
    (hshape : f = C c + (∑ i, C (a i) * X i) + C p * Q)
    (hregular : IsRegular (algebraMap R M p)) :
    ∃ h : MvPolynomial ι R, f = C p * h ∧ h ∈ G.ker := by
  classical
  have hfzero : aeval G.val f = 0 := by
    rwa [ker_eq_ker_aeval_val, RingHom.mem_ker] at hf
  have hpoint : eval₂Hom (algebraMap R S) (fun i => χ (G.val i)) f = 0 := by
    change aeval (fun i => χ (G.val i)) f = 0
    rw [← comp_aeval_apply G.val χ f, hfzero, map_zero]
  obtain ⟨d, hd⟩ := dvd_constant_of_local_eval₂Hom_eq_zero
    (algebraMap R S) p c a f Q (fun i => χ (G.val i)) hp
    (fun i => Ideal.mem_span_singleton.mpr (ha i)) hshape hpoint
  choose b hb using ha
  let h : MvPolynomial ι R := C d + (∑ i, C (b i) * X i) + Q
  have hdiv : f = C p * h := by
    rw [hshape]
    simp only [h, hd, hb, map_mul, mul_add, Finset.mul_sum, mul_assoc]
  refine ⟨h, hdiv, ?_⟩
  rw [ker_eq_ker_aeval_val, RingHom.mem_ker]
  apply hregular.left
  have he := congrArg (aeval G.val) hdiv
  rw [hfzero, map_mul, aeval_C] at he
  simpa only [mul_zero] using he.symm

end Algebra.Generators
