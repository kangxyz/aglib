/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.MonicSpan
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Order
public import Mathlib.Tactic.Ring

/-!
# Quadratics in the square of a closed plane point

A nonzero polynomial of total degree at most two in the square of a maximal
ideal of the affine plane is a scalar linear square if the original residue
extension has degree greater than one. The proof contracts to the original
one-variable coefficient ring and eliminates the second variable by monic
polynomial division. It works in every characteristic without a p-basis or
perfection assumption. Every residue dimension uses the original quotient
and its original coefficient action.
-/

@[expose] public noncomputable section

open scoped Polynomial

namespace Polynomial.QuadraticClosedPoint

universe u

/-- Ordinary differentiation takes the square of an ideal into that ideal. -/
theorem derivative_mem_of_mem_sq {R : Type*} [CommRing R]
    (I : Ideal R[X]) {p : R[X]} (hp : p ∈ I ^ 2) : derivative p ∈ I := by
  rw [pow_two] at hp
  refine Submodule.mul_induction_on hp ?_ ?_
  · intro a ha b hb
    rw [derivative_mul]
    exact I.add_mem (I.mul_mem_left _ hb) (I.mul_mem_right _ ha)
  · intro a b ha hb
    simpa only [map_add] using I.add_mem ha hb

private def monicQuadratic {R : Type*} [CommRing R] (b c : R) : R[X] :=
  X ^ 2 + C b * X + C c

private theorem monicQuadratic_monic {R : Type*} [CommRing R] [Nontrivial R]
    (b c : R) : (monicQuadratic b c).Monic := by
  change (X ^ 2 + C b * X + C c).leadingCoeff = 1
  simpa only [C_1, one_mul] using
    (leadingCoeff_quadratic (a := (1 : R)) (b := b) (c := c) one_ne_zero)

private theorem monicQuadratic_natDegree {R : Type*} [CommRing R] [Nontrivial R]
    (b c : R) : (monicQuadratic b c).natDegree = 2 := by
  simpa only [C_1, one_mul, monicQuadratic] using
    (natDegree_quadratic (a := (1 : R)) (b := b) (c := c) one_ne_zero)

/-- Monic elimination in the original iterated polynomial ring. The residue
quotient and coefficient action remain the original ones. -/
theorem monic_quadratic_mem_sq
    {k : Type u} [Field k] (M : Ideal k[X][X]) [M.IsMaximal]
    (b c : k[X]) (hb : b.natDegree ≤ 1) (hc : c.natDegree ≤ 2)
    (hres : 1 < Module.finrank k (k[X][X] ⧸ M))
    (hF : X ^ 2 + C b * X + C c ∈ M ^ 2) :
    ∃ G : k[X], G.natDegree ≤ 1 ∧ X ^ 2 + C b * X + C c = (X - C G) ^ 2 := by
  classical
  let N : Ideal k[X] := M.comap C
  have hN : N.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing M
  let : N.IsMaximal := hN
  have hN0 : N ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hN (Polynomial.not_isField k)
  obtain ⟨f, hf, hNf⟩ := Polynomial.exists_monic_span N hN0
  have hf1 : f ≠ 1 := by
    intro h
    have : (1 : k[X]) ∈ N := by rw [hNf, h]; exact Ideal.subset_span rfl
    exact hN.ne_top ((Ideal.eq_top_iff_one N).mpr this)
  let K := k[X] ⧸ N
  let : Field K := Ideal.Quotient.field N
  let τ : k[X][X] →+* K[X] := Polynomial.mapRingHom (Ideal.Quotient.mk N)
  have hτker : RingHom.ker τ = N.map C := by
    have hk : RingHom.ker (Ideal.Quotient.mk N) = N := by
      ext r
      change Ideal.Quotient.mk N r = 0 ↔ r ∈ N
      exact Ideal.Quotient.eq_zero_iff_mem
    simp only [τ, Polynomial.ker_mapRingHom]
    rw [hk]
  let F := monicQuadratic b c
  have hFmonic : F.Monic := monicQuadratic_monic b c
  have hFmem : F ∈ M := Ideal.pow_le_self (by decide : (2 : ℕ) ≠ 0) hF
  have hne : M ≠ N.map C := by
    intro he
    have hz : τ F = 0 := by
      change F ∈ RingHom.ker τ
      rw [hτker, ← he]
      exact hFmem
    exact (hFmonic.map (Ideal.Quotient.mk N)).ne_zero hz
  obtain ⟨g, hg, hMg⟩ := Polynomial.exists_monic_span_sup_map_eq
    (R := k[X]) M hN hne
  have hgmem : g ∈ M := by
    rw [hMg]
    exact Submodule.mem_sup_right (Ideal.subset_span rfl)
  have hτN : (N.map C).map τ = ⊥ := by
    apply (Ideal.map_eq_bot_iff_le_ker τ).mpr
    exact hτker.symm.le
  have hτM : M.map τ = Ideal.span {τ g} := by
    rw [hMg, Ideal.map_sup, hτN, bot_sup_eq, Ideal.map_span, Set.image_singleton]
  have hdvd : (τ g) ^ 2 ∣ τ F := by
    apply Ideal.mem_span_singleton.mp
    have h := Ideal.mem_map_of_mem τ hF
    rw [Ideal.map_pow, hτM, Ideal.span_singleton_pow] at h
    exact h
  have hdegF : (τ F).natDegree = 2 := by
    have he : τ F = monicQuadratic (Ideal.Quotient.mk N b) (Ideal.Quotient.mk N c) := by
      simp [τ, F, monicQuadratic]
    rw [he]
    exact monicQuadratic_natDegree _ _
  have hgdeg_le : g.natDegree ≤ 1 := by
    have h := natDegree_le_of_dvd hdvd (hFmonic.map (Ideal.Quotient.mk N)).ne_zero
    rw [natDegree_pow, hdegF] at h
    change 2 * (g.map (Ideal.Quotient.mk N)).natDegree ≤ 2 at h
    rw [hg.natDegree_map] at h
    omega
  have hgdeg : g.natDegree = 1 := by
    by_contra h
    have hzero : g.natDegree = 0 := by omega
    have hg1 : g = 1 := by
      rw [eq_C_of_natDegree_eq_zero hzero]
      have h0 : g.coeff 0 = 1 := by
        simpa only [Monic, leadingCoeff, hzero] using hg
      rw [h0, C_1]
    exact (show M.IsMaximal from inferInstance).ne_top
      ((Ideal.eq_top_iff_one M).mpr (hg1 ▸ hgmem))
  let G0 := -g.coeff 0
  let G := G0 %ₘ f
  have hGdiff : G - G0 ∈ N := by
    rw [hNf]
    exact Ideal.mem_span_singleton.mpr (dvd_modByMonic_sub G0 f)
  have hlin : X - C G ∈ M := by
    have hgform : g = X - C G0 := by simpa [G0] using hg.eq_X_add_C hgdeg
    have hCdiff : C (G - G0) ∈ M := hGdiff
    have heq : X - C G = (X - C G0) - C (G - G0) := by
      simp only [map_sub]
      ring
    rw [heq, ← hgform]
    exact M.sub_mem hgmem hCdiff
  have hcomp : Ideal.Quotient.mk M =
      ((Ideal.Quotient.mk M).comp C).comp (evalRingHom G) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_X]
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hlin
  let ρ : k[X] →ₐ[k] k[X][X] ⧸ M :=
    (Ideal.Quotient.mkₐ k M).comp (Polynomial.CAlgHom (R := k) (A := k[X]))
  have hρ : Function.Surjective ρ := by
    intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨p.eval G, ?_⟩
    exact (RingHom.congr_fun hcomp p).symm
  have hρker : RingHom.ker ρ.toRingHom = N := by
    ext p
    change Ideal.Quotient.mk M (Polynomial.C p) = 0 ↔ Polynomial.C p ∈ M
    exact Ideal.Quotient.eq_zero_iff_mem
  let E : (k[X] ⧸ N) ≃ₐ[k] (k[X][X] ⧸ M) :=
    (Ideal.quotientEquivAlgOfEq k hρker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := ρ) hρ)
  have hdegree : Module.finrank k (k[X][X] ⧸ M) = f.natDegree := by
    rw [← E.toLinearEquiv.finrank_eq, hNf]
    exact finrank_quotient_span_eq_natDegree
  have hd : 1 < f.natDegree := by rwa [hdegree] at hres
  have hG : G.natDegree < f.natDegree := natDegree_modByMonic_lt G0 hf hf1
  have heval : M.map (evalRingHom G) ≤ N := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    change C (p.eval G) ∈ M
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (RingHom.congr_fun hcomp p).symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hp)
  have hvalue : G ^ 2 + b * G + c = 0 := by
    have hmap := Ideal.mem_map_of_mem (evalRingHom G) hF
    rw [Ideal.map_pow] at hmap
    have hmem : (X ^ 2 + C b * X + C c).eval G ∈ N ^ 2 :=
      Ideal.pow_right_mono heval 2 hmap
    simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C] at hmem
    rw [hNf, Ideal.span_singleton_pow] at hmem
    apply eq_zero_of_dvd_of_natDegree_lt (Ideal.mem_span_singleton.mp hmem)
    rw [natDegree_pow]
    have hsq : (G ^ 2).natDegree < 2 * f.natDegree := by rw [natDegree_pow]; omega
    have hmul : (b * G).natDegree < 2 * f.natDegree :=
      natDegree_mul_le.trans_lt (by omega)
    exact (natDegree_add_le _ _).trans_lt (max_lt (by
      exact (natDegree_add_le _ _).trans_lt (max_lt hsq hmul)) (by omega))
  have hderiv : 2 * G + b = 0 := by
    have hmem := derivative_mem_of_mem_sq M hF
    have hmap : (derivative (X ^ 2 + C b * X + C c)).eval G ∈ N :=
      heval (Ideal.mem_map_of_mem (evalRingHom G) hmem)
    have hval : (derivative (X ^ 2 + C b * X + C c)).eval G = 2 * G + b := by
      rw [map_add, map_add, derivative_X_sq, derivative_C_mul_X, derivative_C]
      simp only [eval_add, eval_mul, eval_C, eval_X, add_zero]
    rw [hval, hNf] at hmap
    apply eq_zero_of_dvd_of_natDegree_lt (Ideal.mem_span_singleton.mp hmap)
    have hmul : (2 * G).natDegree ≤ G.natDegree := by
      simpa only [natDegree_ofNat, zero_add] using
        (natDegree_mul_le (p := (2 : k[X])) (q := G))
    exact (natDegree_add_le _ _).trans_lt (max_lt (hmul.trans_lt hG) (by omega))
  have hsquare : X ^ 2 + C b * X + C c = (X - C G) ^ 2 := by
    have he : X ^ 2 + C b * X + C c = (X - C G) ^ 2 +
        C (2 * G + b) * (X - C G) + C (G ^ 2 + b * G + c) := by
      simp only [map_add, map_mul, map_pow, map_ofNat]
      ring
    simpa only [hvalue, hderiv, map_zero, zero_mul, add_zero] using he
  have hcoeff : c = G ^ 2 := by
    have h := congrArg (Polynomial.eval (0 : k[X])) hsquare
    simpa only [eval_add, eval_mul, eval_pow, eval_sub, eval_C, eval_X,
      zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, zero_add,
      add_zero, zero_sub, neg_sq] using h
  have hG1 : G.natDegree ≤ 1 := by
    have h : (G ^ 2).natDegree ≤ 2 := hcoeff ▸ hc
    rw [natDegree_pow] at h
    omega
  exact ⟨G, hG1, hsquare⟩

end Polynomial.QuadraticClosedPoint

namespace MvPolynomial.QuadraticClosedPoint

universe u
variable {k : Type u} [Field k]

/-- An affine linear polynomial in the original two plane coordinates. -/
def linear (a b c : k) : MvPolynomial (Fin 2) k := C a + C b * X 1 + C c * X 0

/-- The six original coefficients of a plane quadratic, with `X 0` the outer variable. -/
def quadratic (a b c d e f : k) : MvPolynomial (Fin 2) k :=
  C a + C b * X 1 + C c * X 0 + C d * X 1 ^ 2 + C e * X 1 * X 0 + C f * X 0 ^ 2

private theorem quadratic_scale (t a b c d e f : k) :
    quadratic (t*a) (t*b) (t*c) (t*d) (t*e) (t*f) = C t * quadratic a b c d e f := by
  simp only [quadratic, map_mul]
  ring

private theorem add_totalDegree_le {p q : MvPolynomial (Fin 2) k} {n : ℕ}
    (hp : p.totalDegree ≤ n) (hq : q.totalDegree ≤ n) : (p+q).totalDegree ≤ n :=
  (totalDegree_add _ _).trans (max_le hp hq)

theorem linear_totalDegree (a b c : k) : (linear a b c).totalDegree ≤ 1 := by
  apply add_totalDegree_le
  · apply add_totalDegree_le
    · simp
    · exact (totalDegree_mul _ _).trans (by simp)
  · exact (totalDegree_mul _ _).trans (by simp)

private theorem quadratic_totalDegree (a b c d e f : k) :
    (quadratic a b c d e f).totalDegree ≤ 2 := by
  have hlin (a : k) (i : Fin 2) : (C a * X i : MvPolynomial (Fin 2) k).totalDegree ≤ 2 :=
    (totalDegree_mul _ _).trans (by simp)
  have hsq (a : k) (i : Fin 2) : (C a * X i ^ 2 : MvPolynomial (Fin 2) k).totalDegree ≤ 2 := by
    apply (totalDegree_mul _ _).trans
    simp
  have hcross : (C e * X 1 * X 0 : MvPolynomial (Fin 2) k).totalDegree ≤ 2 := by
    apply (totalDegree_mul _ _).trans
    have h := totalDegree_mul (C e : MvPolynomial (Fin 2) k) (X 1)
    simp only [totalDegree_C, totalDegree_X, zero_add] at h
    simpa using Nat.add_le_add_right h 1
  exact add_totalDegree_le (add_totalDegree_le (add_totalDegree_le
    (add_totalDegree_le (add_totalDegree_le (by simp) (hlin b 1)) (hlin c 0))
    (hsq d 1)) hcross) (hsq f 0)

private def regroup : MvPolynomial (Fin 2) k ≃ₐ[k] k[X][X] :=
  (MvPolynomial.finSuccEquiv k 1).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv k (Fin 1)))

private theorem regroup_C (a : k) : regroup (C a) = Polynomial.C (Polynomial.C a) := by
  exact (regroup (k := k)).commutes a

private theorem regroup_V : regroup (X 0 : MvPolynomial (Fin 2) k) = Polynomial.X := by
  simp [regroup, MvPolynomial.finSuccEquiv_X_zero]

private theorem regroup_U : regroup (X 1 : MvPolynomial (Fin 2) k) =
    Polynomial.C Polynomial.X := by
  simp only [regroup, AlgEquiv.trans_apply, Polynomial.coe_mapAlgEquiv]
  rw [show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
    MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  have hOne : (MvPolynomial.uniqueAlgEquiv k (Fin 1))
      (MvPolynomial.X 0) = Polynomial.X := by
    change MvPolynomial.eval₂ Polynomial.C
      (fun _ : Fin 1 => (Polynomial.X : k[X])) (MvPolynomial.X 0) = Polynomial.X
    exact MvPolynomial.eval₂_X _ _ _
  exact congrArg Polynomial.C hOne

private theorem regroup_quadratic (a b c d e : k) :
    regroup (quadratic a b c d e 1) =
      Polynomial.X ^ 2 +
        Polynomial.C (Polynomial.C e * Polynomial.X + Polynomial.C c) * Polynomial.X +
        Polynomial.C (Polynomial.C d * Polynomial.X ^ 2 +
          Polynomial.C b * Polynomial.X + Polynomial.C a) := by
  simp only [quadratic, map_add, map_mul, map_pow, regroup_C, regroup_U, regroup_V,
    Polynomial.C_1, one_mul]
  ring

private theorem mapped_residue_degree (M : Ideal (MvPolynomial (Fin 2) k))
    (E : MvPolynomial (Fin 2) k ≃ₐ[k] MvPolynomial (Fin 2) k)
    (h : 1 < Module.finrank k (MvPolynomial (Fin 2) k ⧸ M)) :
    1 < Module.finrank k (MvPolynomial (Fin 2) k ⧸ M.map E.toRingHom) := by
  let e := Ideal.quotientEquivAlg M (M.map E.toRingHom) E rfl
  rw [← e.toLinearEquiv.finrank_eq]
  exact h

private theorem monic_case
    (M : Ideal (MvPolynomial (Fin 2) k)) [M.IsMaximal]
    (hres : 1 < Module.finrank k (MvPolynomial (Fin 2) k ⧸ M))
    (a b c d e : k) (hF : quadratic a b c d e 1 ∈ M ^ 2) :
    ∃ A B C : k, quadratic a b c d e 1 = linear A B C ^ 2 := by
  let N := M.map (regroup (k := k)).toRingHom
  let : N.IsMaximal := (Ideal.isMaximal_map_iff_of_bijective
    (regroup (k := k)).toRingHom (regroup (k := k)).bijective).mpr inferInstance
  let E := Ideal.quotientEquivAlg M N (regroup (k := k)) rfl
  have hNres : 1 < Module.finrank k (k[X][X] ⧸ N) := by
    rw [← E.toLinearEquiv.finrank_eq]
    exact hres
  have hmap := Ideal.mem_map_of_mem (regroup (k := k)).toRingHom hF
  rw [Ideal.map_pow] at hmap
  change regroup (quadratic a b c d e 1) ∈ N ^ 2 at hmap
  rw [regroup_quadratic] at hmap
  obtain ⟨G, hG, hGsq⟩ := Polynomial.QuadraticClosedPoint.monic_quadratic_mem_sq N
    (Polynomial.C e * Polynomial.X + Polynomial.C c)
    (Polynomial.C d * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C a)
    Polynomial.natDegree_linear_le Polynomial.natDegree_quadratic_le hNres hmap
  refine ⟨-G.coeff 0, -G.coeff 1, 1, ?_⟩
  apply (regroup (k := k)).injective
  rw [regroup_quadratic, hGsq, map_pow]
  congr 1
  conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hG]
  simp only [linear, map_add, map_mul, regroup_C, regroup_U, regroup_V,
    map_neg, Polynomial.C_1, one_mul]
  ring

private theorem nonzero_last_case
    (M : Ideal (MvPolynomial (Fin 2) k)) [M.IsMaximal]
    (hres : 1 < Module.finrank k (MvPolynomial (Fin 2) k ⧸ M))
    (a b c d e f : k) (hf : f ≠ 0) (hF : quadratic a b c d e f ∈ M ^ 2) :
    ∃ s : k, s ≠ 0 ∧ ∃ A B C : k,
      quadratic a b c d e f = MvPolynomial.C s * linear A B C ^ 2 := by
  have hscaled : quadratic (f⁻¹*a) (f⁻¹*b) (f⁻¹*c) (f⁻¹*d) (f⁻¹*e) 1 =
      MvPolynomial.C f⁻¹ * quadratic a b c d e f := by
    simpa [hf] using quadratic_scale f⁻¹ a b c d e f
  have hm : quadratic (f⁻¹*a) (f⁻¹*b) (f⁻¹*c) (f⁻¹*d) (f⁻¹*e) 1 ∈ M ^ 2 := by
    rw [hscaled]
    exact (M ^ 2).mul_mem_left _ hF
  obtain ⟨A, B, C, h⟩ := monic_case M hres _ _ _ _ _ hm
  refine ⟨f, hf, A, B, C, ?_⟩
  rw [← h, hscaled, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hf, map_one, one_mul]

private def swap : MvPolynomial (Fin 2) k ≃ₐ[k] MvPolynomial (Fin 2) k :=
  MvPolynomial.renameEquiv k (Equiv.swap 0 1)

private theorem swap_C (a : k) : swap (C a) = (C a : MvPolynomial (Fin 2) k) :=
  (swap (k := k)).commutes a

private theorem swap_linear (a b c : k) : swap (linear a b c) = linear a c b := by
  simp only [swap, linear, MvPolynomial.renameEquiv_apply, map_add, map_mul, rename_C,
    rename_X, Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

private theorem swap_quadratic (a b c d e f : k) :
    swap (quadratic a b c d e f) = quadratic a c b f e d := by
  simp only [swap, quadratic, MvPolynomial.renameEquiv_apply, map_add, map_mul,
    map_pow, rename_C, rename_X, Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

private def shiftHom (r : k) : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval ![X 0, X 1 + C r * X 0]

private theorem shiftHom_comp (r s : k) :
    (shiftHom r).comp (shiftHom s) = shiftHom (r+s) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [shiftHom, MvPolynomial.algebraMap_eq]
  ring

private theorem shiftHom_zero : shiftHom (0 : k) = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [shiftHom]

private def shift (r : k) : MvPolynomial (Fin 2) k ≃ₐ[k] MvPolynomial (Fin 2) k :=
  AlgEquiv.ofAlgHom (shiftHom r) (shiftHom (-r))
    (by rw [shiftHom_comp, add_neg_cancel, shiftHom_zero])
    (by rw [shiftHom_comp, neg_add_cancel, shiftHom_zero])

private theorem shift_C (r a : k) : shift r (C a) = (C a : MvPolynomial (Fin 2) k) :=
  (shift r).commutes a

private theorem shift_linear (r a b c : k) :
    shift r (linear a b c) = linear a b (c+b*r) := by
  simp [shift, shiftHom, linear, MvPolynomial.algebraMap_eq]
  ring

private theorem shift_cross_quadratic (a b c e : k) :
    shift 1 (quadratic a b c 0 e 0) = quadratic a b (c+b) 0 e e := by
  simp [shift, shiftHom, quadratic, MvPolynomial.algebraMap_eq]
  ring

private theorem pderiv_mem_of_mem_sq (M : Ideal (MvPolynomial (Fin 2) k))
    {F : MvPolynomial (Fin 2) k} (hF : F ∈ M ^ 2) (i : Fin 2) : pderiv i F ∈ M := by
  rw [pow_two] at hF
  refine Submodule.mul_induction_on hF ?_ ?_
  · intro a ha b hb
    rw [pderiv_mul]
    exact M.add_mem (M.mul_mem_left _ hb) (M.mul_mem_right _ ha)
  · intro a b ha hb
    simpa only [map_add] using M.add_mem ha hb

private theorem scalar_eq_zero_of_mem (M : Ideal (MvPolynomial (Fin 2) k)) [M.IsMaximal]
    {a : k} (ha : C a ∈ M) : a = 0 := by
  by_contra h
  have h1 : (1 : MvPolynomial (Fin 2) k) ∈ M := by
    have hh := M.mul_mem_left (C a⁻¹) ha
    simpa only [← map_mul, inv_mul_cancel₀ h, map_one] using hh
  exact (show M.IsMaximal from inferInstance).ne_top ((Ideal.eq_top_iff_one M).mpr h1)

/-- The six-coefficient version retains the original maximal ideal and its
original quotient-field action. No characteristic hypothesis is imposed. -/
theorem quadratic_mem_sq
    (M : Ideal (MvPolynomial (Fin 2) k)) [M.IsMaximal]
    (a b c d e f : k) (hF0 : quadratic a b c d e f ≠ 0)
    (hF : quadratic a b c d e f ∈ M ^ 2)
    (hres : 1 < Module.finrank k (MvPolynomial (Fin 2) k ⧸ M)) :
    ∃ s : k, s ≠ 0 ∧ ∃ A B C : k,
      quadratic a b c d e f = MvPolynomial.C s * linear A B C ^ 2 := by
  classical
  by_cases hf : f = 0
  · subst f
    by_cases hd : d = 0
    · subst d
      by_cases he : e = 0
      · subst e
        have hb : b = 0 := scalar_eq_zero_of_mem M (by
          simpa [quadratic] using pderiv_mem_of_mem_sq M hF 1)
        have hc : c = 0 := scalar_eq_zero_of_mem M (by
          simpa [quadratic] using pderiv_mem_of_mem_sq M hF 0)
        subst b
        subst c
        have ha : a = 0 := scalar_eq_zero_of_mem M (by
          simpa [quadratic] using Ideal.pow_le_self (by decide : (2 : ℕ) ≠ 0) hF)
        exact (hF0 (by simp [quadratic, ha])).elim
      · let N := M.map (shift (1 : k)).toRingHom
        let : N.IsMaximal := (Ideal.isMaximal_map_iff_of_bijective _
          (shift (1 : k)).bijective).mpr inferInstance
        have hNres := mapped_residue_degree M (shift (1 : k)) hres
        have hmap := Ideal.mem_map_of_mem (shift (1 : k)).toRingHom hF
        rw [Ideal.map_pow] at hmap
        change shift 1 (quadratic a b c 0 e 0) ∈ N ^ 2 at hmap
        rw [shift_cross_quadratic] at hmap
        obtain ⟨s, hs, A, B, C, h⟩ := nonzero_last_case N hNres a b (c+b) 0 e e he hmap
        refine ⟨s, hs, A, B, C-B, ?_⟩
        apply (shift (1 : k)).injective
        rw [shift_cross_quadratic, h, map_mul, map_pow, shift_C, shift_linear]
        simp
    · let N := M.map (swap (k := k)).toRingHom
      let : N.IsMaximal := (Ideal.isMaximal_map_iff_of_bijective _
        (swap (k := k)).bijective).mpr inferInstance
      have hNres := mapped_residue_degree M (swap (k := k)) hres
      have hmap := Ideal.mem_map_of_mem (swap (k := k)).toRingHom hF
      rw [Ideal.map_pow] at hmap
      change swap (quadratic a b c d e 0) ∈ N ^ 2 at hmap
      rw [swap_quadratic] at hmap
      obtain ⟨s, hs, A, B, C, h⟩ := nonzero_last_case N hNres a c b 0 e d hd hmap
      refine ⟨s, hs, A, C, B, ?_⟩
      apply (swap (k := k)).injective
      simpa only [swap_quadratic, map_mul, map_pow, swap_C, swap_linear] using h
  · exact nonzero_last_case M hres a b c d e f hf hF

private theorem quadratic_monomials (a b c d e f : k) :
    quadratic a b c d e f =
      monomial 0 a + monomial (Finsupp.single 1 1) b + monomial (Finsupp.single 0 1) c +
      monomial (Finsupp.single 1 2) d +
      monomial (Finsupp.single 1 1 + Finsupp.single 0 1) e +
        monomial (Finsupp.single 0 2) f := by
  simp only [quadratic, monomial_zero', monomial_single_add,
    ← C_mul_X_pow_eq_monomial, pow_one]
  ring

private theorem exponent_eq_iff (a b : Fin 2 →₀ ℕ) :
    a = b ↔ a 0 = b 0 ∧ a 1 = b 1 := by
  constructor
  · intro h
    subst b
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0,h1⟩
    ext i
    fin_cases i
    · exact h0
    · exact h1

/-- Every original total-degree-at-most-two polynomial has its literal six
coefficient expansion; this is not a supplied quadratic presentation. -/
theorem eq_quadratic_of_totalDegree_le (F : MvPolynomial (Fin 2) k)
    (hF : F.totalDegree ≤ 2) :
    F = quadratic (F.coeff 0) (F.coeff (Finsupp.single 1 1))
      (F.coeff (Finsupp.single 0 1)) (F.coeff (Finsupp.single 1 2))
      (F.coeff (Finsupp.single 1 1 + Finsupp.single 0 1))
      (F.coeff (Finsupp.single 0 2)) := by
  classical
  let Q := quadratic (F.coeff 0) (F.coeff (Finsupp.single 1 1))
    (F.coeff (Finsupp.single 0 1)) (F.coeff (Finsupp.single 1 2))
    (F.coeff (Finsupp.single 1 1 + Finsupp.single 0 1)) (F.coeff (Finsupp.single 0 2))
  have hQ : Q.totalDegree ≤ 2 := quadratic_totalDegree ..
  ext d
  have hd : d = Finsupp.single 1 (d 1) + Finsupp.single 0 (d 0) := by
    ext i
    fin_cases i <;> simp
  have hsum : ∑ i ∈ d.support, d i = d 0 + d 1 := by
    change d.sum (fun _ n => n) = _
    rw [Finsupp.sum_fintype _ _ (by intro i; rfl)]
    simp [Fin.sum_univ_succ]
  by_cases hsmall : d 0 + d 1 ≤ 2
  · have hcases : (d 0 = 0 ∧ d 1 = 0) ∨ (d 0 = 0 ∧ d 1 = 1) ∨
        (d 0 = 1 ∧ d 1 = 0) ∨ (d 0 = 0 ∧ d 1 = 2) ∨
        (d 0 = 1 ∧ d 1 = 1) ∨ (d 0 = 2 ∧ d 1 = 0) := by omega
    rcases hcases with ⟨h0,h1⟩ | ⟨h0,h1⟩ | ⟨h0,h1⟩ | ⟨h0,h1⟩ | ⟨h0,h1⟩ | ⟨h0,h1⟩ <;>
      rw [hd] <;>
      simp [quadratic_monomials, h0, h1, exponent_eq_iff]
  · have hlt : 2 < ∑ i ∈ d.support, d i := by rw [hsum]; omega
    change F.coeff d = Q.coeff d
    rw [coeff_eq_zero_of_totalDegree_lt (hF.trans_lt hlt),
      coeff_eq_zero_of_totalDegree_lt (hQ.trans_lt hlt)]

end MvPolynomial.QuadraticClosedPoint

namespace MvPolynomial

universe u

/-- A nonzero plane quadratic in the square of an actual nonrational closed
point is a literal nonzero scalar times an affine linear square. The dimension
is for the original quotient and the original constant coefficient action. -/
theorem exists_scalar_linear_sq_of_mem_maximal_sq
    {k : Type u} [Field k] (M : Ideal (MvPolynomial (Fin 2) k)) [M.IsMaximal]
    (F : MvPolynomial (Fin 2) k) (hF0 : F ≠ 0) (hdeg : F.totalDegree ≤ 2)
    (hF : F ∈ M ^ 2) (hres : 1 < Module.finrank k (MvPolynomial (Fin 2) k ⧸ M)) :
    ∃ c : k, c ≠ 0 ∧ ∃ l : MvPolynomial (Fin 2) k,
      l ≠ 0 ∧ l.totalDegree ≤ 1 ∧ F = C c * l ^ 2 := by
  obtain ⟨a,b,c,d,e,f,h⟩ : ∃ a b c d e f : k, F =
      QuadraticClosedPoint.quadratic a b c d e f := by
    exact ⟨_, _, _, _, _, _, QuadraticClosedPoint.eq_quadratic_of_totalDegree_le F hdeg⟩
  have hQ0 : QuadraticClosedPoint.quadratic a b c d e f ≠ 0 := by
    intro hz
    exact hF0 (h.trans hz)
  obtain ⟨s, hs, A, B, C, hsq⟩ := QuadraticClosedPoint.quadratic_mem_sq M a b c d e f
    hQ0 (h ▸ hF) hres
  refine ⟨s, hs, QuadraticClosedPoint.linear A B C, ?_,
    QuadraticClosedPoint.linear_totalDegree A B C, h.trans hsq⟩
  intro hz
  exact hF0 (by rw [h, hsq, hz, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero])

end MvPolynomial
