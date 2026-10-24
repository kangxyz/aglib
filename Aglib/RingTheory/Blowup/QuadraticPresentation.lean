/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.GradedAlgebra.MonicQuadratic
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Order
public import Aglib.RingTheory.Blowup.CaseOne
public import Aglib.RingTheory.AssociatedGraded.Cotangent.Graded
public import Aglib.RingTheory.ReesAlgebra.ExceptionalChart
public import Mathlib.RingTheory.Polynomial.Quotient

/-!
# Quadratic tangent cones and their actual exceptional presentations

The final theorem derives the entire original canonical kernel and the precise
CaseOne.Presentation from the original ideal generators and the genuine Hilbert
function. All coordinate changes are undone before the original blowup chart is
used. Rationality, Gorenstein duality, and the Hilbert-function supplier remain
upstream hypotheses of the geometric application.
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial
open scoped Polynomial BigOperators

universe u v

namespace GradedAlgebra.TernaryQuadratic

variable {k : Type u} [Field k]

/-- The six distinct degree-two exponents in the original ordered variables. -/
def exponent : Fin 6 → Fin 3 →₀ ℕ :=
  ![Finsupp.single 0 2, Finsupp.single 1 2, Finsupp.single 2 2,
    Finsupp.single 0 1 + Finsupp.single 1 1,
    Finsupp.single 0 1 + Finsupp.single 2 1,
    Finsupp.single 1 1 + Finsupp.single 2 1]

theorem exponent_injective : Function.Injective exponent := by
  intro i j h
  have h0 := congrArg (fun d : Fin 3 →₀ ℕ => d 0) h
  have h1 := congrArg (fun d : Fin 3 →₀ ℕ => d 1) h
  fin_cases i <;> fin_cases j <;>
    solve
    | rfl
    | norm_num [exponent] at h0
    | norm_num [exponent] at h1

theorem exponent_degree (i : Fin 6) : (exponent i).degree = 2 := by
  fin_cases i <;> simp [exponent]

/-- A coefficient vector in the six original quadratic monomials. -/
def quadratic (a : Fin 6 → k) : MvPolynomial (Fin 3) k :=
  ∑ i, monomial (exponent i) (a i)

theorem quadratic_coeff (a : Fin 6 → k) (i : Fin 6) :
    (quadratic a).coeff (exponent i) = a i := by
  rw [quadratic, MvPolynomial.coeff_sum, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp only [MvPolynomial.coeff_monomial,
      ite_eq_right (fun h => hji (exponent_injective h))]
  · simp

theorem quadratic_injective : Function.Injective (quadratic (k := k)) := by
  intro a b h
  funext i
  simpa only [quadratic_coeff] using congrArg (fun p => p.coeff (exponent i)) h

theorem quadratic_add (a b : Fin 6 → k) : quadratic (a + b) = quadratic a + quadratic b := by
  simp only [quadratic, Pi.add_apply, map_add, Finset.sum_add_distrib]

theorem quadratic_smul (r : k) (a : Fin 6 → k) : quadratic (r • a) = r • quadratic a := by
  simp only [quadratic, Pi.smul_apply, ← MvPolynomial.smul_monomial, Finset.smul_sum]

theorem quadratic_homogeneous (a : Fin 6 → k) : (quadratic a).IsHomogeneous 2 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  exact MvPolynomial.isHomogeneous_monomial (a i) (exponent_degree i)

theorem quadratic_expansion (a : Fin 6 → k) : quadratic a =
    C (a 0) * X 0 ^ 2 + C (a 1) * X 1 ^ 2 + C (a 2) * X 2 ^ 2 +
      C (a 3) * X 0 * X 1 + C (a 4) * X 0 * X 2 + C (a 5) * X 1 * X 2 := by
  simp only [quadratic, Fin.sum_univ_succ, exponent, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
  simp only [MvPolynomial.monomial_add_single, ← MvPolynomial.C_mul_X_pow_eq_monomial,
    pow_one]
  change (C (a 0) * X 0 ^ 2 : MvPolynomial (Fin 3) k) +
    (C (a 1) * X 1 ^ 2 + (C (a 2) * X 2 ^ 2 +
      (C (a 3) * X 0 * X 1 + (C (a 4) * X 0 * X 2 + C (a 5) * X 1 * X 2)))) = _
  ring

/-- A linear substitution preserves every homogeneous degree when its variables have degree one. -/
theorem homogeneous_map (F : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 3) k)
    (hF : ∀ i, (F (X i)).IsHomogeneous 1) {n : ℕ}
    {p : MvPolynomial (Fin 3) k} (hp : p.IsHomogeneous n) : (F p).IsHomogeneous n := by
  have h : MvPolynomial.aeval (fun i => F (X i)) = F := by
    apply MvPolynomial.algHom_ext
    intro i
    exact MvPolynomial.aeval_X _ _
  rw [← h]
  simpa only [one_mul] using hp.aeval (fun i => F (X i)) hF

/-- A constructed invertible homogeneous coordinate change; no coordinate data is assumed later. -/
structure LinearCoordinates (k : Type u) [Field k] where
  /-- The original polynomial algebra equivalence underlying the homogeneous coordinate change. -/
  equiv : MvPolynomial (Fin 3) k ≃ₐ[k] MvPolynomial (Fin 3) k
  variableHomogeneous : ∀ i, (equiv (X i)).IsHomogeneous 1
  inverseVariableHomogeneous : ∀ i, (equiv.symm (X i)).IsHomogeneous 1

namespace LinearCoordinates

@[simp] theorem equiv_C (E : LinearCoordinates k) (a : k) : E.equiv (C a) = C a :=
  E.equiv.commutes a

@[simp] theorem symm_C (E : LinearCoordinates k) (a : k) : E.equiv.symm (C a) = C a :=
  E.equiv.symm.commutes a

/-- The identity homogeneous coordinate change. -/
def refl : LinearCoordinates k where
  equiv := AlgEquiv.refl
  variableHomogeneous := MvPolynomial.isHomogeneous_X k
  inverseVariableHomogeneous := MvPolynomial.isHomogeneous_X k

/-- Compose homogeneous coordinate changes, applying `E` first and then `F`. -/
def trans (E F : LinearCoordinates k) : LinearCoordinates k where
  equiv := E.equiv.trans F.equiv
  variableHomogeneous i := homogeneous_map F.equiv.toAlgHom F.variableHomogeneous
    (E.variableHomogeneous i)
  inverseVariableHomogeneous i := homogeneous_map E.equiv.symm.toAlgHom
    E.inverseVariableHomogeneous (F.inverseVariableHomogeneous i)

/-- The homogeneous coordinate change interchanging variables zero and `j`. -/
def swap (j : Fin 3) : LinearCoordinates k where
  equiv := MvPolynomial.renameEquiv k (Equiv.swap 0 j)
  variableHomogeneous i := by
    simpa only [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X] using
      MvPolynomial.isHomogeneous_X k ((Equiv.swap 0 j) i)
  inverseVariableHomogeneous i := by
    simpa only [MvPolynomial.renameEquiv_symm, MvPolynomial.renameEquiv_apply,
      MvPolynomial.rename_X] using
        MvPolynomial.isHomogeneous_X k ((Equiv.swap 0 j).symm i)

@[simp] theorem swap_X (j i : Fin 3) :
    (swap (k := k) j).equiv (X i) = X ((Equiv.swap 0 j) i) := by
  change MvPolynomial.rename (Equiv.swap 0 j) (X i) = _
  exact MvPolynomial.rename_X _ _

/-- Add the first variable to one specified other variable. -/
def shear (j : Fin 3) (hj : j ≠ 0) : LinearCoordinates k := by
  let f : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 3) k :=
    MvPolynomial.aeval fun i => if i = j then X i + X 0 else X i
  let g : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 3) k :=
    MvPolynomial.aeval fun i => if i = j then X i - X 0 else X i
  have hfg : f.comp g = AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases hi : i = j
    · subst i
      simp [f, g, hj.symm]
    · simp [f, g, hi]
  have hgf : g.comp f = AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases hi : i = j
    · subst i
      simp [f, g, hj.symm]
    · simp [f, g, hi]
  refine ⟨AlgEquiv.ofAlgHom f g hfg hgf, ?_, ?_⟩
  · intro i
    change (f (X i)).IsHomogeneous 1
    rw [show f (X i) = if i = j then X i + X 0 else X i from MvPolynomial.aeval_X _ _]
    split_ifs
    · exact (MvPolynomial.isHomogeneous_X k i).add (MvPolynomial.isHomogeneous_X k 0)
    · exact MvPolynomial.isHomogeneous_X k i
  · intro i
    change (g (X i)).IsHomogeneous 1
    rw [show g (X i) = if i = j then X i - X 0 else X i from MvPolynomial.aeval_X _ _]
    split_ifs
    · exact (MvPolynomial.isHomogeneous_X k i).sub (MvPolynomial.isHomogeneous_X k 0)
    · exact MvPolynomial.isHomogeneous_X k i

@[simp] theorem shear_X (j : Fin 3) (hj : j ≠ 0) (i : Fin 3) :
    (shear (k := k) j hj).equiv (X i) = if i = j then X i + X 0 else X i :=
  MvPolynomial.aeval_X _ _

end LinearCoordinates

theorem swap_one_quadratic (a : Fin 6 → k) :
    (LinearCoordinates.swap (k := k) 1).equiv (quadratic a) =
      quadratic ![a 1, a 0, a 2, a 3, a 5, a 4] := by
  rw [quadratic_expansion, quadratic_expansion]
  simp only [map_add, map_mul, map_pow, LinearCoordinates.equiv_C,
    LinearCoordinates.swap_X]
  norm_num [Equiv.swap_apply_def]
  ring

theorem swap_two_quadratic (a : Fin 6 → k) :
    (LinearCoordinates.swap (k := k) 2).equiv (quadratic a) =
      quadratic ![a 2, a 1, a 0, a 5, a 4, a 3] := by
  rw [quadratic_expansion, quadratic_expansion]
  simp only [map_add, map_mul, map_pow, LinearCoordinates.equiv_C,
    LinearCoordinates.swap_X]
  norm_num [Equiv.swap_apply_def]
  ring

theorem shear_one_quadratic (a : Fin 6 → k) :
    (LinearCoordinates.shear (k := k) 1 (by decide)).equiv (quadratic a) =
      quadratic ![a 0 + a 1 + a 3, a 1, a 2, a 1 + a 1 + a 3, a 4 + a 5, a 5] := by
  rw [quadratic_expansion, quadratic_expansion]
  simp only [map_add, map_mul, map_pow, LinearCoordinates.equiv_C,
    LinearCoordinates.shear_X]
  norm_num
  ring

theorem shear_two_quadratic (a : Fin 6 → k) :
    (LinearCoordinates.shear (k := k) 2 (by decide)).equiv (quadratic a) =
      quadratic ![a 0 + a 2 + a 4, a 1, a 2, a 3 + a 5, a 2 + a 2 + a 4, a 5] := by
  rw [quadratic_expansion, quadratic_expansion]
  simp only [map_add, map_mul, map_pow, LinearCoordinates.equiv_C,
    LinearCoordinates.shear_X]
  norm_num
  ring

/-- A nonzero quadratic is made monic by actual swaps and shears, in every characteristic. -/
theorem exists_nonzero_leading_coordinate (a : Fin 6 → k) (ha : a ≠ 0) :
    ∃ E : LinearCoordinates k, ∃ b : Fin 6 → k,
      b 0 ≠ 0 ∧ E.equiv (quadratic a) = quadratic b := by
  by_cases h0 : a 0 ≠ 0
  · exact ⟨LinearCoordinates.refl, a, h0, rfl⟩
  by_cases h1 : a 1 ≠ 0
  · exact ⟨LinearCoordinates.swap 1, _, h1, swap_one_quadratic a⟩
  by_cases h2 : a 2 ≠ 0
  · exact ⟨LinearCoordinates.swap 2, _, h2, swap_two_quadratic a⟩
  have h0' : a 0 = 0 := not_ne_iff.mp h0
  have h1' : a 1 = 0 := not_ne_iff.mp h1
  have h2' : a 2 = 0 := not_ne_iff.mp h2
  by_cases h3 : a 3 ≠ 0
  · refine ⟨LinearCoordinates.shear 1 (by decide), _, ?_, shear_one_quadratic a⟩
    simpa only [Matrix.cons_val_zero, h0', h1', zero_add] using h3
  by_cases h4 : a 4 ≠ 0
  · refine ⟨LinearCoordinates.shear 2 (by decide), _, ?_, shear_two_quadratic a⟩
    simpa only [Matrix.cons_val_zero, h0', h2', zero_add] using h4
  have h5 : a 5 ≠ 0 := by
    intro h5
    apply ha
    funext i
    fin_cases i <;> simp_all
  let b : Fin 6 → k := ![a 1, a 0, a 2, a 3, a 5, a 4]
  refine ⟨(LinearCoordinates.swap 1).trans (LinearCoordinates.shear 2 (by decide)),
    ![b 0 + b 2 + b 4, b 1, b 2, b 3 + b 5, b 2 + b 2 + b 4, b 5], ?_, ?_⟩
  · simpa [b, h1', h2'] using h5
  · change (LinearCoordinates.shear 2 (by decide)).equiv
      ((LinearCoordinates.swap 1).equiv (quadratic a)) = _
    rw [swap_one_quadratic]
    exact shear_two_quadratic b

/-- The mixed linear coefficient after normalizing the first squared coordinate by `b 0`. -/
def linearPart (b : Fin 6 → k) : MvPolynomial (Fin 2) k :=
  C ((b 0)⁻¹ * b 3) * X 0 + C ((b 0)⁻¹ * b 4) * X 1

/-- The remaining binary quadratic part scaled by the inverse of `b 0`. -/
def binaryPart (b : Fin 6 → k) : MvPolynomial (Fin 2) k :=
  C ((b 0)⁻¹ * b 1) * X 0 ^ 2 + C ((b 0)⁻¹ * b 2) * X 1 ^ 2 +
    C ((b 0)⁻¹ * b 5) * X 0 * X 1

theorem linearPart_homogeneous (b : Fin 6 → k) : (linearPart b).IsHomogeneous 1 :=
  (MvPolynomial.isHomogeneous_C_mul_X _ _).add (MvPolynomial.isHomogeneous_C_mul_X _ _)

theorem binaryPart_homogeneous (b : Fin 6 → k) : (binaryPart b).IsHomogeneous 2 := by
  apply ((MvPolynomial.isHomogeneous_C_mul_X_pow _ _ _).add
    (MvPolynomial.isHomogeneous_C_mul_X_pow _ _ _)).add
  simpa only [mul_assoc] using ((MvPolynomial.isHomogeneous_X k 0).mul
    (MvPolynomial.isHomogeneous_X k 1)).C_mul ((b 0)⁻¹ * b 5)

theorem monic_relation (b : Fin 6 → k) (hb : b 0 ≠ 0) :
    MonicQuadratic.relation (linearPart b) (binaryPart b) = C ((b 0)⁻¹) * quadratic b := by
  have hunit : C ((b 0)⁻¹) * C (b 0) = (1 : MvPolynomial (Fin 3) k) := by
    rw [← map_mul, inv_mul_cancel₀ hb, map_one]
  rw [MonicQuadratic.relation, quadratic_expansion]
  simp only [linearPart, binaryPart, MonicQuadratic.binaryInclusion,
    map_add, map_mul, map_pow, MvPolynomial.rename_C, MvPolynomial.rename_X]
  norm_num
  linear_combination -(X (R := k) (0 : Fin 3) ^ 2) * hunit

section Target

attribute [local instance] MvPolynomial.gradedAlgebra

variable {G : Type v} [CommRing G] [Algebra k G]
  (H : ℕ → Submodule k G) [GradedAlgebra H]
  (π : MvPolynomial.homogeneousSubmodule (Fin 3) k →ₐᵍ[k] H)

/-- The six original quadratic coefficients map into the original degree-two component. -/
def quadraticMap : (Fin 6 → k) →ₗ[k] H 2 where
  toFun a := ⟨π (quadratic a), π.map_mem
    ((MvPolynomial.mem_homogeneousSubmodule 2 _).mpr (quadratic_homogeneous a))⟩
  map_add' a b := by
    apply Subtype.ext
    change π (quadratic (a + b)) = π (quadratic a) + π (quadratic b)
    rw [quadratic_add, map_add]
  map_smul' r a := by
    apply Subtype.ext
    change π (quadratic (r • a)) = r • π (quadratic a)
    rw [quadratic_smul]
    exact map_smul π.toAlgHom r (quadratic a)

/-- The genuine degree-two Hilbert dimension produces a nonzero original relation. -/
theorem exists_quadratic_relation (hH : Module.finrank k (H 2) = 5) :
    ∃ a : Fin 6 → k, a ≠ 0 ∧ π (quadratic a) = 0 := by
  let : Module.Finite k (H 2) := Module.finite_of_finrank_pos (by rw [hH]; decide)
  have hdim : Module.finrank k (Fin 6 → k) = 6 := by
    rw [Module.finrank_pi]
    rfl
  have hker : LinearMap.ker (quadraticMap H π) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (f := quadraticMap H π)
      (by rw [hH, hdim]; decide)
  have hex : ∃ a : Fin 6 → k, a ≠ 0 ∧ quadraticMap H π a = 0 := by
    by_contra hn
    apply hker
    apply LinearMap.ker_eq_bot'.mpr
    intro a ha
    by_contra ha0
    exact hn ⟨a, ha0, ha⟩
  obtain ⟨a, ha, hmap⟩ := hex
  have hx := congrArg (fun z : H 2 => (z : G)) hmap
  change π (quadratic a) = 0 at hx
  exact ⟨a, ha, hx⟩

/-- Precompose the original map with the actual inverse homogeneous coordinate change. -/
def transformedMap (E : LinearCoordinates k) :
    MvPolynomial.homogeneousSubmodule (Fin 3) k →ₐᵍ[k] H where
  __ := π.toAlgHom.comp E.equiv.symm.toAlgHom
  map_mem := by
    intro n p hp
    apply π.map_mem
    exact (MvPolynomial.mem_homogeneousSubmodule n _).mpr
      (homogeneous_map E.equiv.symm.toAlgHom E.inverseVariableHomogeneous
        ((MvPolynomial.mem_homogeneousSubmodule n p).mp hp))

/-- All genuine Hilbert dimensions determine the full kernel of the ORIGINAL map. -/
theorem exists_original_kernel_coefficients (hπ : Function.Surjective π)
    (hHilbert : ∀ n, Module.finrank k (H n) = 2 * n + 1) :
    ∃ a : Fin 6 → k,
      a ≠ 0 ∧ RingHom.ker π.toAlgHom = Ideal.span {quadratic a} := by
  obtain ⟨a, ha, hqa⟩ := exists_quadratic_relation H π (by simpa using hHilbert 2)
  obtain ⟨E, b, hb, hE⟩ := exists_nonzero_leading_coordinate a ha
  let π' := transformedMap H π E
  have hπ' : Function.Surjective π' := hπ.comp E.equiv.symm.surjective
  have hrel : π' (MonicQuadratic.relation (linearPart b) (binaryPart b)) = 0 := by
    change π (E.equiv.symm (MonicQuadratic.relation (linearPart b) (binaryPart b))) = 0
    rw [monic_relation b hb, ← hE, map_mul, LinearCoordinates.symm_C,
      AlgEquiv.symm_apply_apply, map_mul, hqa, mul_zero]
  have hk' := MonicQuadratic.kernel_eq_span H π' (linearPart b) (binaryPart b)
    (linearPart_homogeneous b) (binaryPart_homogeneous b) hπ' hrel hHilbert
  refine ⟨a, ha, le_antisymm ?_ ?_⟩
  · intro p hp
    have hp' : E.equiv p ∈ RingHom.ker π'.toAlgHom := by
      change π (E.equiv.symm (E.equiv p)) = 0
      rw [AlgEquiv.symm_apply_apply]
      exact hp
    rw [hk'] at hp'
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hp'
    apply Ideal.mem_span_singleton.mpr
    refine ⟨C ((b 0)⁻¹) * E.equiv.symm r, ?_⟩
    have h := congrArg E.equiv.symm hr
    rw [AlgEquiv.symm_apply_apply, monic_relation b hb, ← hE,
      map_mul, map_mul, LinearCoordinates.symm_C, AlgEquiv.symm_apply_apply] at h
    calc
      p = C ((b 0)⁻¹) * quadratic a * E.equiv.symm r := h
      _ = quadratic a * (C ((b 0)⁻¹) * E.equiv.symm r) := by ring
  · exact (Ideal.span_singleton_le_iff_mem (RingHom.ker π.toAlgHom)).mpr hqa

/-- A nonzero homogeneous equation generates the entire original canonical kernel. -/
theorem exists_original_kernel (hπ : Function.Surjective π)
    (hHilbert : ∀ n, Module.finrank k (H n) = 2 * n + 1) :
    ∃ q : MvPolynomial (Fin 3) k,
      q ≠ 0 ∧ q.IsHomogeneous 2 ∧ RingHom.ker π.toAlgHom = Ideal.span {q} := by
  obtain ⟨a, ha, hker⟩ := exists_original_kernel_coefficients H π hπ hHilbert
  refine ⟨quadratic a, ?_, quadratic_homogeneous a, hker⟩
  intro hz
  apply ha
  apply quadratic_injective
  simpa only [quadratic, Pi.zero_apply, map_zero, Finset.sum_const_zero] using hz

end Target
end GradedAlgebra.TernaryQuadratic

namespace MvPolynomial.FirstCoordinate

variable {k : Type u} [Field k]

/-- The original first-coordinate dehomogenizing ideal. -/
def coordinateIdeal : Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span ({X (R := k) (0 : Fin 3) - 1} : Set (MvPolynomial (Fin 3) k))

/-- Substitute one for the first original variable; retain the other ordered variables. -/
def dehom : MvPolynomial (Fin 3) k →+* MvPolynomial (Fin 2) k :=
  (Polynomial.evalRingHom 1).comp (MvPolynomial.finSuccEquiv k 2).toRingHom

@[simp] theorem dehom_C (a : k) : dehom (C a) = (C a : MvPolynomial (Fin 2) k) := by
  change Polynomial.eval 1 (MvPolynomial.finSuccEquiv k 2 (C a)) = C a
  rw [show MvPolynomial.finSuccEquiv k 2 (C a) = Polynomial.C (C a) from
    (MvPolynomial.finSuccEquiv k 2).commutes a, Polynomial.eval_C]

@[simp] theorem dehom_X_zero : dehom (X 0) = (1 : MvPolynomial (Fin 2) k) := by
  change Polynomial.eval 1 (MvPolynomial.finSuccEquiv k 2 (X 0)) = 1
  rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.eval_X]

@[simp] theorem dehom_X_succ (i : Fin 2) :
    dehom (X i.succ) = (X i : MvPolynomial (Fin 2) k) := by
  change Polynomial.eval 1 (MvPolynomial.finSuccEquiv k 2 (X i.succ)) = X i
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.eval_C]

/-- The original binary inclusion is a right inverse to dehomogenization. -/
theorem dehom_binaryInclusion (p : MvPolynomial (Fin 2) k) :
    dehom (GradedAlgebra.MonicQuadratic.binaryInclusion p) = p := by
  change Polynomial.eval 1 (MvPolynomial.finSuccEquiv k 2
    (GradedAlgebra.MonicQuadratic.binaryInclusion p)) = p
  rw [GradedAlgebra.MonicQuadratic.finSuccEquiv_binaryInclusion, Polynomial.eval_C]

theorem dehom_surjective : Function.Surjective (dehom (k := k)) :=
  fun p => ⟨GradedAlgebra.MonicQuadratic.binaryInclusion p, dehom_binaryInclusion p⟩

/-- The exact kernel of the original first-coordinate evaluation. -/
theorem ker_dehom : RingHom.ker (dehom (k := k)) = coordinateIdeal (k := k) := by
  let e := MvPolynomial.finSuccEquiv k 2
  have hmap : (coordinateIdeal (k := k)).map
      e.toRingHom = Ideal.span {Polynomial.X - Polynomial.C (1 : MvPolynomial (Fin 2) k)} := by
    rw [coordinateIdeal, Ideal.map_span, Set.image_singleton]
    change Ideal.span {MvPolynomial.finSuccEquiv k 2 (X 0 - 1)} = _
    rw [map_sub, map_one, MvPolynomial.finSuccEquiv_X_zero, Polynomial.C_1]
  rw [dehom, ← RingHom.comap_ker, Polynomial.ker_evalRingHom, ← hmap]
  exact Ideal.comap_map_of_bijective e.toRingHom e.bijective

/-- The original coordinate quotient, with its evaluation map. -/
def dehomQuotientEquiv :
    (MvPolynomial (Fin 3) k ⧸ coordinateIdeal (k := k)) ≃+* MvPolynomial (Fin 2) k :=
  (Ideal.quotEquivOfEq (ker_dehom (k := k)).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := dehom (k := k)) (dehom_surjective (k := k)))

@[simp] theorem dehomQuotientEquiv_mk (p : MvPolynomial (Fin 3) k) :
    dehomQuotientEquiv (Ideal.Quotient.mk (coordinateIdeal (k := k)) p) = dehom p := by
  rw [dehomQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

section Cone

variable {G : Type u} [CommRing G] (π : MvPolynomial (Fin 3) k →+* G)
  (hπ : Function.Surjective π) (q : MvPolynomial (Fin 3) k)
  (hker : RingHom.ker π = Ideal.span {q})

/-- The quotient by the derived original kernel, before dehomogenization. -/
def coneQuotientEquiv : (MvPolynomial (Fin 3) k ⧸ Ideal.span {q}) ≃+* G :=
  (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hπ)

@[simp] theorem coneQuotientEquiv_mk (p : MvPolynomial (Fin 3) k) :
    coneQuotientEquiv π hπ q hker (Ideal.Quotient.mk (Ideal.span {q}) p) = π p := by
  rw [coneQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

@[simp] theorem coneQuotientEquiv_symm_map (p : MvPolynomial (Fin 3) k) :
    (coneQuotientEquiv π hπ q hker).symm (π p) = Ideal.Quotient.mk (Ideal.span {q}) p := by
  apply (coneQuotientEquiv π hπ q hker).injective
  rw [RingEquiv.apply_symm_apply, coneQuotientEquiv_mk]

theorem coordinateIdeal_map : Ideal.span {π (X 0) - 1} =
    ((coordinateIdeal (k := k)).map
      (Ideal.Quotient.mk (Ideal.span {q}))).map
        (coneQuotientEquiv π hπ q hker).toRingHom := by
  rw [Ideal.map_map, coordinateIdeal, Ideal.map_span, Set.image_singleton]
  change Ideal.span {π (X 0) - 1} =
    Ideal.span {coneQuotientEquiv π hπ q hker
      (Ideal.Quotient.mk (Ideal.span {q}) (X 0 - 1))}
  rw [coneQuotientEquiv_mk, map_sub, map_one]

theorem equationIdeal_map : Ideal.span {dehom q} =
    ((Ideal.span {q}).map (Ideal.Quotient.mk (coordinateIdeal (k := k)))).map
      dehomQuotientEquiv.toRingHom := by
  rw [Ideal.map_map, Ideal.map_span, Set.image_singleton]
  change Ideal.span {dehom q} =
    Ideal.span {dehomQuotientEquiv (Ideal.Quotient.mk (coordinateIdeal (k := k)) q)}
  rw [dehomQuotientEquiv_mk]

/-- The actual cone quotient at the original first coordinate is the actual
binary quotient by the dehomogenization of the original equation. -/
def curveQuotientEquiv : (G ⧸ Ideal.span {π (X 0) - 1}) ≃+*
    (MvPolynomial (Fin 2) k ⧸ Ideal.span {dehom q}) :=
  (Ideal.quotientEquiv _ _ (coneQuotientEquiv π hπ q hker)
    (coordinateIdeal_map π hπ q hker)).symm.trans
      ((DoubleQuot.quotQuotEquivComm (Ideal.span {q}) (coordinateIdeal (k := k))).trans
        (Ideal.quotientEquiv _ _ dehomQuotientEquiv (equationIdeal_map q)))

/-- The comparison retains every original polynomial numerator. -/
theorem curveQuotientEquiv_mk_map (p : MvPolynomial (Fin 3) k) :
    curveQuotientEquiv π hπ q hker
      (Ideal.Quotient.mk (Ideal.span {π (X 0) - 1}) (π p)) =
      Ideal.Quotient.mk (Ideal.span {dehom q}) (dehom p) := by
  let e₀ := Ideal.quotientEquiv _ _ (coneQuotientEquiv π hπ q hker)
    (coordinateIdeal_map π hπ q hker)
  let e₁ := DoubleQuot.quotQuotEquivComm (Ideal.span {q}) (coordinateIdeal (k := k))
  let e₂ := Ideal.quotientEquiv _ _ dehomQuotientEquiv (equationIdeal_map q)
  have h₀ : e₀.symm (Ideal.Quotient.mk (Ideal.span {π (X 0) - 1}) (π p)) =
      DoubleQuot.quotQuotMk (Ideal.span {q}) (coordinateIdeal (k := k)) p :=
    (Ideal.quotientEquiv_symm_mk
      ((coordinateIdeal (k := k)).map (Ideal.Quotient.mk (Ideal.span {q})))
      (Ideal.span {π (X 0) - 1}) (coneQuotientEquiv π hπ q hker)
      (coordinateIdeal_map π hπ q hker) (π p)).trans
        (congrArg (Ideal.Quotient.mk
          ((coordinateIdeal (k := k)).map (Ideal.Quotient.mk (Ideal.span {q}))))
            (coneQuotientEquiv_symm_map π hπ q hker p))
  change e₂ (e₁ (e₀.symm (Ideal.Quotient.mk _ (π p)))) = _
  calc
    _ = e₂ (e₁ (DoubleQuot.quotQuotMk (Ideal.span {q}) (coordinateIdeal (k := k)) p)) :=
      congrArg (fun z => e₂ (e₁ z)) h₀
    _ = e₂ (DoubleQuot.quotQuotMk (coordinateIdeal (k := k)) (Ideal.span {q}) p) :=
      congrArg e₂ (DoubleQuot.quotQuotEquivComm_quotQuotMk
        (Ideal.span {q}) (coordinateIdeal (k := k)) p)
    _ = Ideal.Quotient.mk (Ideal.span {dehom q}) (dehom p) :=
      (Ideal.quotientEquiv_mk _ _ dehomQuotientEquiv (equationIdeal_map q)
        (Ideal.Quotient.mk (coordinateIdeal (k := k)) p)).trans
          (congrArg (Ideal.Quotient.mk (Ideal.span {dehom q})) (dehomQuotientEquiv_mk p))

end Cone
end MvPolynomial.FirstCoordinate

namespace Localization.Away.CaseOne

open MvPolynomial.FirstCoordinate

variable {A : Type u} [CommRing A] [IsLocalRing A]
  (t : maximalIdeal A) (g : Fin 2 → maximalIdeal A)

/-- The native quotient commutative-ring structure on the original associated graded ring. -/
local instance associatedGradedCommRing : CommRing (maximalIdeal A).associatedGraded :=
  Ideal.Quotient.commRing (maximalIdeal A).associatedGradedIdeal

/-- The native quotient commutative-semiring structure on the original associated graded ring. -/
local instance associatedGradedCommSemiring :
    CommSemiring (maximalIdeal A).associatedGraded :=
  Ideal.Quotient.commSemiring (maximalIdeal A).associatedGradedIdeal

/-- The displayed original parameters in their original order. -/
def orderedGenerators : Fin 3 → maximalIdeal A := Fin.cons t g

/-- The literal original coefficient-linear tangent-cone map. -/
def canonicalConeMap : MvPolynomial (Fin 3) (ResidueField A) →+*
    (maximalIdeal A).associatedGraded :=
  (Ideal.cotangentPolynomialMap (maximalIdeal A) (orderedGenerators t g)).toRingHom

theorem canonicalConeMap_X (i : Fin 3) : canonicalConeMap t g (MvPolynomial.X i) =
    Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
      (reesAlgebra.degreeOne (maximalIdeal A) (orderedGenerators t g i)) :=
  Ideal.cotangentPolynomialMap_X (maximalIdeal A) (orderedGenerators t g) i

theorem canonicalConeMap_C_residue (a : A) :
    canonicalConeMap t g (MvPolynomial.C (residue A a)) =
      algebraMap A (maximalIdeal A).associatedGraded a :=
  Ideal.cotangentPolynomialMap_C_mk (maximalIdeal A) (orderedGenerators t g) a

variable (hgen : Ideal.span (Set.range fun i => (orderedGenerators t g i : A)) = maximalIdeal A)

include hgen in
theorem canonicalConeMap_surjective : Function.Surjective (canonicalConeMap t g) :=
  Ideal.cotangentPolynomialMap_surjective_of_cotangent_span (maximalIdeal A)
    (orderedGenerators t g)
      (Ideal.cotangent_span_of_ideal_span (maximalIdeal A) (orderedGenerators t g) hgen)

variable (q : MvPolynomial (Fin 3) (ResidueField A))
  (hker : RingHom.ker (canonicalConeMap t g) = Ideal.span {q})

/-- The native degree-one denominator is the image of the ORIGINAL first variable. -/
theorem denominator_eq :
    Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
      (reesAlgebra.degreeOne (maximalIdeal A) t) =
        canonicalConeMap t g (MvPolynomial.X 0) := by
  rw [canonicalConeMap_X]
  rfl

/-- The dehomogenizing ideal retains the same original denominator. -/
theorem denominatorIdeal_eq :
    HomogeneousLocalization.Away.dehomogenizingIdeal
      (f := Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
        (reesAlgebra.degreeOne (maximalIdeal A) t)) =
      Ideal.span {canonicalConeMap t g (MvPolynomial.X 0) - 1} := by
  rw [HomogeneousLocalization.Away.dehomogenizingIdeal, denominator_eq t g]

/-- The actual exceptional quotient is dehomogenized using the original full kernel. -/
def presentationEquivOfKernel :
    ((saturatedChart A (maximalIdeal A) (t : A)) ⧸
      Ideal.span {algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A)}) ≃+*
      (Plane A ⧸ Ideal.span {dehom q}) :=
  (reesAlgebra.exceptionalChartEquiv (maximalIdeal A) t).trans
    ((HomogeneousLocalization.Away.degreeOneQuotientEquiv
      (maximalIdeal A).associatedGradedGrading
      (reesAlgebra.degreeOne_associatedGraded_mem (maximalIdeal A) t)).trans
        ((Ideal.quotEquivOfEq (denominatorIdeal_eq t g)).trans
            (curveQuotientEquiv (canonicalConeMap t g)
              (canonicalConeMap_surjective t g hgen) q hker)))

/-- Original coefficients survive both quotient comparisons. -/
theorem presentationEquivOfKernel_coefficient (a : A) :
    presentationEquivOfKernel t g hgen q hker
      (Ideal.Quotient.mk
        (Ideal.span {algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A)})
        (algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) a)) =
      Ideal.Quotient.mk (Ideal.span {dehom q}) (MvPolynomial.C (residue A a)) := by
  change curveQuotientEquiv (canonicalConeMap t g)
    (canonicalConeMap_surjective t g hgen) q hker
    (Ideal.quotEquivOfEq (denominatorIdeal_eq t g)
      (HomogeneousLocalization.Away.degreeOneQuotientEquiv
        (maximalIdeal A).associatedGradedGrading
        (reesAlgebra.degreeOne_associatedGraded_mem (maximalIdeal A) t)
      (reesAlgebra.exceptionalChartEquiv (maximalIdeal A) t
        (Ideal.Quotient.mk
        (Ideal.span {algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A)})
        (algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) a))))) = _
  rw [reesAlgebra.exceptionalChartEquiv_mk_base]
  have he :
      HomogeneousLocalization.Away.degreeOneQuotientEquiv
        (maximalIdeal A).associatedGradedGrading
        (reesAlgebra.degreeOne_associatedGraded_mem (maximalIdeal A) t)
        (HomogeneousLocalization.Away.dehomogenize
          (maximalIdeal A).associatedGradedGrading
          (reesAlgebra.degreeOne_associatedGraded_mem (maximalIdeal A) t)
          (Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
            (algebraMap A (reesAlgebra (maximalIdeal A)) a))) =
        Ideal.Quotient.mk
          (HomogeneousLocalization.Away.dehomogenizingIdeal
            (f := Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
              (reesAlgebra.degreeOne (maximalIdeal A) t)))
          (Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
            (algebraMap A (reesAlgebra (maximalIdeal A)) a)) :=
    HomogeneousLocalization.Away.toQuotient_dehomogenize
      (maximalIdeal A).associatedGradedGrading
      (reesAlgebra.degreeOne_associatedGraded_mem (maximalIdeal A) t)
      (Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
        (algebraMap A (reesAlgebra (maximalIdeal A)) a))
  rw [he, Ideal.quotEquivOfEq_mk]
  change curveQuotientEquiv (canonicalConeMap t g)
    (canonicalConeMap_surjective t g hgen) q hker
    (Ideal.Quotient.mk (Ideal.span {canonicalConeMap t g (MvPolynomial.X 0) - 1})
      (algebraMap A (maximalIdeal A).associatedGraded a)) = _
  rw [← canonicalConeMap_C_residue t g a, curveQuotientEquiv_mk_map, dehom_C]

/-- Original fraction coordinates survive both quotient comparisons. -/
theorem presentationEquivOfKernel_coordinate (i : Fin 2) :
    presentationEquivOfKernel t g hgen q hker
      (Ideal.Quotient.mk
        (Ideal.span {algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A)})
        (SaturatedChart.fractionElement (maximalIdeal A) t (g i))) =
      Ideal.Quotient.mk (Ideal.span {dehom q}) (MvPolynomial.X i) := by
  change curveQuotientEquiv (canonicalConeMap t g)
    (canonicalConeMap_surjective t g hgen) q hker
    (Ideal.quotEquivOfEq (denominatorIdeal_eq t g)
      (HomogeneousLocalization.Away.degreeOneQuotientEquiv
        (maximalIdeal A).associatedGradedGrading
        (reesAlgebra.degreeOne_associatedGraded_mem (maximalIdeal A) t)
      (reesAlgebra.exceptionalChartEquiv (maximalIdeal A) t
        (Ideal.Quotient.mk
        (Ideal.span {algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A)})
          (SaturatedChart.fractionElement (maximalIdeal A) t (g i)))))) = _
  rw [reesAlgebra.exceptionalChartEquiv_mk_fraction,
    HomogeneousLocalization.Away.degreeOneQuotientEquiv_mk, Ideal.quotEquivOfEq_mk]
  have hnum : canonicalConeMap t g (MvPolynomial.X i.succ) =
      Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
        (reesAlgebra.degreeOne (maximalIdeal A) (g i)) := by
    rw [canonicalConeMap_X]
    rfl
  rw [← hnum, curveQuotientEquiv_mk_map, dehom_X_succ]

/-- The exact object consumed by the CaseOne local core, once the full
original canonical kernel has been derived. -/
def presentationOfKernel : Presentation A t g (dehom q) where
  equiv := presentationEquivOfKernel t g hgen q hker
  coefficient := presentationEquivOfKernel_coefficient t g hgen q hker
  coordinate := presentationEquivOfKernel_coordinate t g hgen q hker

/-- The constructed reduction has exactly the original exceptional ideal as kernel. -/
theorem presentationOfKernel_reduction_ker :
    RingHom.ker (presentationOfKernel t g hgen q hker).reduction = exceptionalIdeal A t := by
  let D := presentationOfKernel t g hgen q hker
  change RingHom.ker (D.equiv.toRingHom.comp (Ideal.Quotient.mk (exceptionalIdeal A t))) = _
  rw [RingHom.ker_comp_of_injective (Ideal.Quotient.mk (exceptionalIdeal A t))
    D.equiv.injective, Ideal.mk_ker]

end Localization.Away.CaseOne


namespace GradedAlgebra.TernaryQuadratic

open MvPolynomial MvPolynomial.FirstCoordinate

variable {k : Type u} [Field k]

/-- The six original exponents after setting the first coordinate to one. -/
def affineExponent : Fin 6 → Fin 2 →₀ ℕ :=
  ![0, Finsupp.single 0 2, Finsupp.single 1 2, Finsupp.single 0 1,
    Finsupp.single 1 1, Finsupp.single 0 1 + Finsupp.single 1 1]

theorem affineExponent_injective : Function.Injective affineExponent := by
  intro i j h
  have h0 := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
  have h1 := congrArg (fun d : Fin 2 →₀ ℕ => d 1) h
  fin_cases i <;> fin_cases j <;>
    solve
    | rfl
    | norm_num [affineExponent] at h0
    | norm_num [affineExponent] at h1

theorem affineExponent_degree_le (i : Fin 6) : (affineExponent i).degree ≤ 2 := by
  fin_cases i <;> simp [affineExponent]

/-- No quadratic coefficient is lost in this fixed homogeneous degree. -/
theorem dehom_quadratic (a : Fin 6 → k) :
    dehom (quadratic a) = ∑ i, monomial (affineExponent i) (a i) := by
  rw [quadratic_expansion]
  have h1 : dehom (X (R := k) (1 : Fin 3)) = X (0 : Fin 2) := dehom_X_succ 0
  have h2 : dehom (X (R := k) (2 : Fin 3)) = X (1 : Fin 2) := dehom_X_succ 1
  simp only [map_add, map_mul, map_pow, dehom_C, dehom_X_zero, h1, h2,
    one_pow, mul_one]
  simp only [Fin.sum_univ_succ, affineExponent, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
  simp only [MvPolynomial.monomial_add_single, ← MvPolynomial.C_mul_X_pow_eq_monomial,
    pow_one, ← MvPolynomial.C_apply]
  change _ = (C (a 0) : MvPolynomial (Fin 2) k) +
    (C (a 1) * X 0 ^ 2 + (C (a 2) * X 1 ^ 2 +
      (C (a 3) * X 0 + (C (a 4) * X 1 + C (a 5) * X 0 * X 1))))
  ring

theorem dehom_quadratic_coeff (a : Fin 6 → k) (i : Fin 6) :
    (dehom (quadratic a)).coeff (affineExponent i) = a i := by
  rw [dehom_quadratic, MvPolynomial.coeff_sum, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp only [MvPolynomial.coeff_monomial,
      ite_eq_right (fun h => hji (affineExponent_injective h))]
  · simp

theorem dehom_quadratic_ne_zero (a : Fin 6 → k) (ha : a ≠ 0) :
    dehom (quadratic a) ≠ 0 := by
  intro hz
  apply ha
  funext i
  simpa only [dehom_quadratic_coeff, AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply, Pi.zero_apply] using
    congrArg (fun p : MvPolynomial (Fin 2) k => p.coeff (affineExponent i)) hz

theorem dehom_quadratic_totalDegree (a : Fin 6 → k) :
    (dehom (quadratic a)).totalDegree ≤ 2 := by
  rw [dehom_quadratic]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  apply (MvPolynomial.totalDegree_monomial_le (affineExponent i) (a i)).trans
  simpa only [Finsupp.degree_apply, Finsupp.sum, Function.id_def] using
    affineExponent_degree_le i

end GradedAlgebra.TernaryQuadratic

namespace Localization.Away.CaseOne

open MvPolynomial.FirstCoordinate

variable {A : Type u} [CommRing A] [IsLocalRing A]
  (t : maximalIdeal A) (g : Fin 2 → maximalIdeal A)
  (hgen : Ideal.span (Set.range fun i => (orderedGenerators t g i : A)) = maximalIdeal A)

attribute [local instance] associatedGradedCommRing associatedGradedCommSemiring
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The original residue-field algebra structure on the native associated graded ring. -/
local instance originalResidueAlgebra :
    Algebra (ResidueField A) (maximalIdeal A).associatedGraded :=
  Ideal.associatedGradedQuotientAlgebra (maximalIdeal A)

/-- The original residue-field module structure on the degree-`n` homogeneous component. -/
local instance originalComponentModule (n : ℕ) :
    Module (ResidueField A) (Ideal.associatedGradedQuotientGrading (maximalIdeal A) n) :=
  Submodule.module (Ideal.associatedGradedQuotientGrading (maximalIdeal A) n)

/-- The full quadratic kernel already forces the displayed original denominator to be nonzero. -/
theorem denominator_ne_zero_of_kernel
    (q : MvPolynomial (Fin 3) (ResidueField A)) (hq0 : q ≠ 0) (hq : q.IsHomogeneous 2)
    (hker : RingHom.ker (canonicalConeMap t g) = Ideal.span {q}) : (t : A) ≠ 0 := by
  intro ht
  have ht' : t = 0 := Subtype.ext ht
  have hz : reesAlgebra.degreeOne (maximalIdeal A) (0 : maximalIdeal A) = 0 := by
    apply Subtype.ext
    simp [reesAlgebra.degreeOne_val]
  have hx : canonicalConeMap t g (MvPolynomial.X 0) = 0 := by
    rw [canonicalConeMap_X]
    change Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
      (reesAlgebra.degreeOne (maximalIdeal A) t) = 0
    rw [ht', hz, map_zero]
  have hmem : MvPolynomial.X (R := ResidueField A) (0 : Fin 3) ∈ Ideal.span {q} := by
    rw [← hker]
    exact hx
  have hd := MvPolynomial.totalDegree_le_of_dvd_of_isDomain
    (Ideal.mem_span_singleton.mp hmem) (MvPolynomial.X_ne_zero (0 : Fin 3))
  rw [hq.totalDegree hq0, MvPolynomial.totalDegree_X] at hd
  omega

include hgen in
/-- The genuine Hilbert function produces the entire original cone kernel and
the actual exceptional quotient required by the CaseOne core.
The rational/Gorenstein source of the Hilbert function is not asserted here. -/
theorem exists_presentation_of_hilbert
    (hHilbert : ∀ n, Module.finrank (ResidueField A)
      (Ideal.associatedGradedQuotientGrading (maximalIdeal A) n) = 2 * n + 1) :
    ∃ q : MvPolynomial (Fin 3) (ResidueField A),
      q ≠ 0 ∧ q.IsHomogeneous 2 ∧
      RingHom.ker (canonicalConeMap t g) = Ideal.span {q} ∧
      (t : A) ≠ 0 ∧ dehom q ≠ 0 ∧ (dehom q).totalDegree ≤ 2 ∧
      Nonempty (Presentation A t g (dehom q)) := by
  let H : ℕ → Submodule (ResidueField A) (maximalIdeal A).associatedGraded :=
    Ideal.associatedGradedQuotientGrading (maximalIdeal A)
  let : GradedAlgebra H := Ideal.associatedGradedQuotientGradedAlgebra (maximalIdeal A)
  let π : MvPolynomial.homogeneousSubmodule (Fin 3) (ResidueField A) →ₐᵍ[ResidueField A] H :=
    Ideal.cotangentGradedPolynomialMap (maximalIdeal A) (orderedGenerators t g)
  have hπ : Function.Surjective π := Ideal.cotangentGradedPolynomialMap_surjective
    (maximalIdeal A) (orderedGenerators t g) hgen
  obtain ⟨a, ha, hker⟩ :=
    GradedAlgebra.TernaryQuadratic.exists_original_kernel_coefficients H π hπ hHilbert
  let q := GradedAlgebra.TernaryQuadratic.quadratic a
  have hq0 : q ≠ 0 := by
    intro hz
    apply ha
    apply GradedAlgebra.TernaryQuadratic.quadratic_injective
    simpa only [q, GradedAlgebra.TernaryQuadratic.quadratic, Pi.zero_apply,
      map_zero, Finset.sum_const_zero] using hz
  have hk : RingHom.ker (canonicalConeMap t g) = Ideal.span {q} := hker
  exact ⟨q, hq0, GradedAlgebra.TernaryQuadratic.quadratic_homogeneous a, hk,
    denominator_ne_zero_of_kernel t g q hq0
      (GradedAlgebra.TernaryQuadratic.quadratic_homogeneous a) hk,
    GradedAlgebra.TernaryQuadratic.dehom_quadratic_ne_zero a ha,
    GradedAlgebra.TernaryQuadratic.dehom_quadratic_totalDegree a,
    ⟨presentationOfKernel t g hgen q hk⟩⟩

end Localization.Away.CaseOne
