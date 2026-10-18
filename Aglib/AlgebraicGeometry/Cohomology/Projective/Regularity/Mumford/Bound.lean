/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Mumford.Hyperplane
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.GlobalGeneration
public import Mathlib.Algebra.MvPolynomial.Monad
public import Aglib.RingTheory.Binomial

/-!
# Mumford's bound, by induction on hyperplane sections

This leaf proves Nitsure, arXiv:math/0504590v1, Thm 2.3 (p. 11; after Mumford, *Lectures on
curves on an algebraic surface*) over a field `k` under the premise that hyperplane sections
exist: every pair of coherent modules admits a common nonzerodivisor
`μ : O(-1) ⊗ - ⟶ 𝟭` (`HasHyperplaneSections`). Over an infinite field the premise holds
(`hasHyperplaneSections_of_infinite`, `Mumford/InfiniteField.lean`: a linear form avoids the
finitely many associated points, Nitsure, p. 10), and `Mumford/ArbitraryField.lean` reduces an
arbitrary field to its algebraic closure (Nitsure, p. 12).

The induction never leaves `P^n`. The ambient modules `G` replace Nitsure's `O_H^p`: they are
coherent, `0`-regular, and satisfy `h⁰(G(r)) ≤ p (r + 1)^{n+1}` for `r ≥ 0`; hyperplane sections
keep these properties (`IsProjectiveRegular.of_hyperplane_restrict`, `hyperplane_dim_zero_le`).
The Hilbert function of `F` is written `χ(F(r)) = Σᵢ aᵢ C(r - s, i)` with a shift `s`; a
hyperplane section shifts the coefficients (`hilbertSum_sub`), raises `s` by one and lowers
the number `N` of possibly nonzero coefficients by one. When `N = 0` the Hilbert function
vanishes and the module is zero (`isZero_of_projectiveHilbertFunction_eq_zero`).

The bound `mumfordBound n p N` has integer coefficients. Nitsure (p. 13) bounds
`h¹(F(m₀)) = h⁰(F(m₀)) - χ(F(m₀))` by `p C(n + m₀, n) - Σᵢ aᵢ C(m₀, i)`, which has rational
coefficients. Here the index is `m₀ - 1` (`IsProjectiveRegular.of_hyperplane_euler`), and
`h¹(F(m₀ - 1)) = h⁰(F(m₀ - 1)) - χ(F(m₀ - 1))` is dominated, for `y = m₀ - 1 - s ≥ 0`, by
`h⁰ ≤ p m₀^{n+1}` and `-aᵢ C(y, i) ≤ aᵢ² (m₀ - 1)ⁱ`, since regularity is upward closed.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-! ### Binomial bookkeeping -/

section Algebra

/-- The Hilbert sum `Σ_{i ≤ n} aᵢ C(x, i)`, with `C = Ring.choose`. -/
def hilbertSum (n : ℕ) (a : Fin (n + 1) → ℤ) (x : ℤ) : ℤ :=
  ∑ i : Fin (n + 1), a i * Ring.choose x i

/-- The shifted coefficient vector `bⱼ = a_{j+1}`, `b_n = 0`. -/
def coeffShift (n : ℕ) (a : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ :=
  fun j => if h : j.val + 1 < n + 1 then a ⟨j.val + 1, h⟩ else 0

/-- The shift as a substitution of polynomials. -/
def coeffShiftPoly (n : ℕ) : Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℤ :=
  fun j => if h : j.val + 1 < n + 1 then MvPolynomial.X ⟨j.val + 1, h⟩ else 0

theorem eval_coeffShiftPoly (n : ℕ) (a : Fin (n + 1) → ℤ) (j : Fin (n + 1)) :
    MvPolynomial.eval a (coeffShiftPoly n j) = coeffShift n a j := by
  unfold coeffShiftPoly coeffShift
  split_ifs <;> simp

theorem eval_bind₁_coeffShiftPoly (n : ℕ) (a : Fin (n + 1) → ℤ)
    (P : MvPolynomial (Fin (n + 1)) ℤ) :
    MvPolynomial.eval a (MvPolynomial.bind₁ (coeffShiftPoly n) P) =
      MvPolynomial.eval (coeffShift n a) P := by
  have h := MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℤ) a (coeffShiftPoly n) P
  change MvPolynomial.eval₂Hom (RingHom.id ℤ) a (MvPolynomial.bind₁ (coeffShiftPoly n) P) =
    MvPolynomial.eval₂Hom (RingHom.id ℤ) (coeffShift n a) P
  have hf : (fun i => MvPolynomial.eval₂Hom (RingHom.id ℤ) a (coeffShiftPoly n i)) =
      coeffShift n a :=
    funext fun j => eval_coeffShiftPoly n a j
  rw [h, hf]

/-- The difference of Hilbert sums is the Hilbert sum of the shifted coefficients. -/
theorem hilbertSum_sub (n : ℕ) (a : Fin (n + 1) → ℤ) (x : ℤ) :
    hilbertSum n a x - hilbertSum n a (x - 1) = hilbertSum n (coeffShift n a) (x - 1) := by
  unfold hilbertSum
  rw [← Finset.sum_sub_distrib, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [Fin.val_zero, Ring.choose_zero_right, sub_self, Fin.val_succ, Fin.val_castSucc,
    Fin.val_last, ← mul_sub, Ring.choose_succ_sub_choose_pred, zero_add]
  have hlast : coeffShift n a (Fin.last n) = 0 := by
    unfold coeffShift
    simp
  rw [hlast, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold coeffShift
  split_ifs with h
  · rfl
  · exact absurd (by simp only [Fin.val_castSucc]; omega) h

/-- The coefficient vector of a shift has one fewer possibly nonzero entry. -/
theorem coeffShift_eq_zero (n : ℕ) (a : Fin (n + 1) → ℤ) (N : ℕ)
    (ha : ∀ i : Fin (n + 1), N + 1 ≤ i.val → a i = 0) (j : Fin (n + 1)) (hj : N ≤ j.val) :
    coeffShift n a j = 0 := by
  unfold coeffShift
  split_ifs with h
  · exact ha _ (by simp only; omega)
  · rfl

/-- `-Σᵢ aᵢ C(y, i) ≤ Σᵢ aᵢ² zⁱ` for `0 ≤ y ≤ z`. -/
theorem neg_hilbertSum_le (n : ℕ) (a : Fin (n + 1) → ℤ) {y z : ℤ} (hy : 0 ≤ y) (hz : y ≤ z) :
    -hilbertSum n a y ≤ ∑ i : Fin (n + 1), a i ^ 2 * z ^ (i : ℕ) := by
  unfold hilbertSum
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => (Ring.neg_mul_choose_le (a i) hy i).trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hz i) (sq_nonneg _)

/-- Mumford's bound: `B_0 = 0` and, with `m₀ = (B_N ∘ shift)² + n + 2`,
`B_{N+1} = m₀ + p m₀^{n+1} + Σᵢ Xᵢ² (m₀ - 1)ⁱ`. -/
def mumfordBound (n p : ℕ) : ℕ → MvPolynomial (Fin (n + 1)) ℤ
  | 0 => 0
  | N + 1 =>
    (MvPolynomial.bind₁ (coeffShiftPoly n) (mumfordBound n p N) ^ 2 +
        ((n + 2 : ℕ) : MvPolynomial (Fin (n + 1)) ℤ)) +
      (p : MvPolynomial (Fin (n + 1)) ℤ) *
        (MvPolynomial.bind₁ (coeffShiftPoly n) (mumfordBound n p N) ^ 2 +
          ((n + 2 : ℕ) : MvPolynomial (Fin (n + 1)) ℤ)) ^ (n + 1) +
      ∑ i : Fin (n + 1), MvPolynomial.X i ^ 2 *
        (MvPolynomial.bind₁ (coeffShiftPoly n) (mumfordBound n p N) ^ 2 +
          ((n + 2 : ℕ) : MvPolynomial (Fin (n + 1)) ℤ) - 1) ^ (i : ℕ)

theorem eval_mumfordBound_succ (n p N : ℕ) (a : Fin (n + 1) → ℤ) :
    MvPolynomial.eval a (mumfordBound n p (N + 1)) =
      ((MvPolynomial.eval (coeffShift n a) (mumfordBound n p N)) ^ 2 + (n + 2 : ℕ)) +
        p * ((MvPolynomial.eval (coeffShift n a) (mumfordBound n p N)) ^ 2 + (n + 2 : ℕ)) ^
          (n + 1) +
        ∑ i : Fin (n + 1), a i ^ 2 *
          ((MvPolynomial.eval (coeffShift n a) (mumfordBound n p N)) ^ 2 + (n + 2 : ℕ) - 1) ^
            (i : ℕ) := by
  rw [mumfordBound]
  simp only [map_add, map_mul, map_pow, map_sum, map_sub, map_one, map_natCast,
    MvPolynomial.eval_X, eval_bind₁_coeffShiftPoly]

end Algebra

/-! ### Zero modules -/

section Zero

variable {R : Type u} [CommRing R] {ι : Type u}

/-- Vanishing of a twist depends only on the value of the twist degree. -/
theorem isZero_twist_congr {F : (ProjectiveSpace R ι).Modules} {c c' : ℤ} (h : c = c')
    (hc : IsZero ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι c)).obj F)) :
    IsZero ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι c')).obj F) := by
  subst h
  exact hc

/-- A module with a vanishing twist vanishes. -/
theorem isZero_of_isZero_twist {F : (ProjectiveSpace R ι).Modules} (m : ℤ)
    (hm : IsZero ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι m)).obj F)) :
    IsZero F := by
  have h1 := (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (-m))).map_isZero hm
  have h2 : IsZero ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
      (twistingSheaf R ι (-m + m))).obj F) := by
    have := h1.of_iso ((twistingTensorCompIso R ι (-m) m).app F).symm
    simpa only [Functor.comp_obj] using this
  have h3 := isZero_twist_congr (neg_add_cancel m) h2
  exact h3.of_iso ((twistingTensorZeroIso R ι).app F).symm

end Zero

section Field

variable {k : Type u} [Field k] {ι : Type u}

/-- **A coherent module with vanishing Hilbert function is zero**: for `r` large, `O(r) ⊗ F` is
globally generated with `h⁰ = χ = 0` (Nitsure, Lemma 2.1 (c)). -/
theorem isZero_of_projectiveHilbertFunction_eq_zero (n : ℕ) (e : ι ≃ Fin (n + 1))
    {F : (ProjectiveSpace k ι).Modules} (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F)
    (h : ∀ r : ℤ, projectiveHilbertFunction k ι F r = 0) : IsZero F := by
  have : Finite ι := Finite.of_equiv _ e.symm
  obtain ⟨m, hm⟩ := exists_isProjectiveRegular k ι n e F hF
  have hM := twistingTensor_affineLocallyFiniteType k ι m F hF
  have hvan (q : ℕ) (hq : q ≠ 0) : projectiveCohomologyDim k ι
      ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι m)).obj F) q = 0 :=
    projectiveCohomologyDim_eq_zero_of_subsingleton
      (IsProjectiveRegular.cohomology_subsingleton_of_le_of_coherent k ι n e hF hm le_rfl
        (Nat.pos_of_ne_zero hq))
  have hχ : projectiveHilbertFunction k ι F m = projectiveCohomologyDim k ι
      ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι m)).obj F) 0 := by
    unfold projectiveHilbertFunction projectiveEulerChar
    rw [finsum_eq_single _ 0 (fun q hq => by rw [hvan q hq, Nat.cast_zero, mul_zero])]
    simp
  have h0 : projectiveCohomologyDim k ι
      ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι m)).obj F) 0 = 0 := by
    have := h m
    omega
  have hsub := subsingleton_of_projectiveCohomologyDim_eq_zero n e hM h0
  have hepi := IsProjectiveRegular.epi_globalSectionsEval k ι n e hF hm le_rfl
  have hzero : globalSectionsEval ((moduleTensorLeftFunctor (ProjectiveSpace k ι)
      (twistingSheaf k ι m)).obj F) = 0 := by
    apply Sigma.hom_ext
    intro s
    rw [ι_globalSectionsEval, unitHom_eq_zero_of_subsingleton hsub s, comp_zero]
    rfl
  exact isZero_of_isZero_twist m (IsZero.of_epi_eq_zero _ hzero)

/-! ### The induction -/

/-- **Hyperplane sections exist**: every pair of coherent modules has a common nonzerodivisor
`μ : O(-1) ⊗ - ⟶ 𝟭`. Over an infinite field with finitely many coordinates, multiplication by a
linear form avoiding the associated points of both modules is one (Nitsure,
arXiv:math/0504590v1, p. 10; `hasHyperplaneSections_of_infinite`). -/
def HasHyperplaneSections (k : Type u) [Field k] (ι : Type u) : Prop :=
  ∀ G Q : (ProjectiveSpace k ι).Modules, affineLocallyFiniteType (ProjectiveSpace k ι) G →
    affineLocallyFiniteType (ProjectiveSpace k ι) Q →
      ∃ μ : moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (-1)) ⟶
          𝟭 (ProjectiveSpace k ι).Modules,
        Mono (μ.app G) ∧ Mono (μ.app Q)

/-- The ambient modules of the induction: coherent, `0`-regular, with
`h⁰(G(r)) ≤ p (r + 1)^{n+1}` for every `r ≥ 0`. -/
structure IsMumfordAmbient (n p : ℕ) (G : (ProjectiveSpace k ι).Modules) : Prop where
  coherent : affineLocallyFiniteType (ProjectiveSpace k ι) G
  regular : IsProjectiveRegular k ι G 0
  dim_le : ∀ r : ℤ, 0 ≤ r → (projectiveCohomologyDim k ι
    ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι r)).obj G) 0 : ℤ) ≤
      p * (r + 1) ^ (n + 1)

/-- Hyperplane sections of ambient modules are ambient. -/
theorem IsMumfordAmbient.hyperplane {n p : ℕ} (e : ι ≃ Fin (n + 1))
    {G : (ProjectiveSpace k ι).Modules} (hG : IsMumfordAmbient n p G)
    (μ : moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (-1)) ⟶
      𝟭 (ProjectiveSpace k ι).Modules) [Mono (μ.app G)] :
    IsMumfordAmbient n p (cokernel (μ.app G)) where
  coherent :=
    have : Finite ι := Finite.of_equiv _ e.symm
    hyperplane_affineLocallyFiniteType μ hG.coherent
  regular := IsProjectiveRegular.of_hyperplane_restrict (hyperplaneSequence μ G) (Iso.refl _)
    (hyperplaneSequence_shortExact μ G) hG.regular
  dim_le r hr := by
    have h1 := IsProjectiveRegular.subsingleton_of_le_add n e hG.coherent (s := r + -1) (q := 1)
      hG.regular one_pos (by push_cast; omega)
    have h := hyperplane_dim_zero_le (hyperplaneSequence μ G) (Iso.refl _) n e
      (hyperplaneSequence_shortExact μ G) hG.coherent r h1
    exact (Nat.cast_le.mpr h).trans (hG.dim_le r hr)

/-- **Mumford's induction** (Nitsure, arXiv:math/0504590v1, proof of Thm 2.3, pp. 12-13), on the
number `N` of possibly nonzero Hilbert coefficients, with shift `s = n + 1 - N`. -/
theorem isProjectiveRegular_mumfordBound_aux (n p : ℕ) (e : ι ≃ Fin (n + 1))
    (hgen : HasHyperplaneSections k ι) :
    ∀ (N : ℕ), N ≤ n + 1 → ∀ (F G : (ProjectiveSpace k ι).Modules) (j : F ⟶ G), Mono j →
      affineLocallyFiniteType (ProjectiveSpace k ι) F → IsMumfordAmbient n p G →
      ∀ a : Fin (n + 1) → ℤ, (∀ i : Fin (n + 1), N ≤ i.val → a i = 0) →
      (∀ r : ℤ, projectiveHilbertFunction k ι F r = hilbertSum n a (r - ((n + 1 - N : ℕ) : ℤ))) →
      IsProjectiveRegular k ι F (MvPolynomial.eval a (mumfordBound n p N)) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  intro N
  induction N with
  | zero =>
    intro _ F G j _ hF _ a ha hχ
    refine IsProjectiveRegular.of_isZero
      (isZero_of_projectiveHilbertFunction_eq_zero n e hF fun r => ?_) _
    rw [hχ r]
    unfold hilbertSum
    exact Finset.sum_eq_zero fun i _ => by rw [ha i (Nat.zero_le _), zero_mul]
  | succ N ih =>
    intro hN F G j hj hF hG a ha hχ
    have hQ : affineLocallyFiniteType (ProjectiveSpace k ι) (cokernel j) :=
      (affineLocallyFiniteType (ProjectiveSpace k ι)).prop_cokernel j hF hG.coherent
    obtain ⟨μ, hμG, hμQ⟩ := hgen G (cokernel j) hG.coherent hQ
    have hμF : Mono (μ.app F) := mono_app_of_mono j
    have hjH := mono_hyperplaneCokernelMap μ j
    have hFH := hyperplane_affineLocallyFiniteType μ hF
    -- the shift of the Hilbert function
    have hχH (r : ℤ) : projectiveHilbertFunction k ι (cokernel (μ.app F)) r =
        hilbertSum n (coeffShift n a) (r - ((n + 1 - N : ℕ) : ℤ)) := by
      rw [projectiveHilbertFunction_hyperplane μ n e F hF r, hχ r, hχ (r - 1)]
      have h := hilbertSum_sub n a (r - ((n + 1 - (N + 1) : ℕ) : ℤ))
      have e1 : ((n + 1 - N : ℕ) : ℤ) = n + 1 - N := by omega
      have e2 : ((n + 1 - (N + 1) : ℕ) : ℤ) = n - N := by omega
      rw [e2] at h
      rw [e1, e2, show r - 1 - (n - N : ℤ) = r - (n - N) - 1 by ring, h]
      ring_nf
    have hregH := ih (by omega) _ _ (hyperplaneCokernelMap μ j) hjH hFH (hG.hyperplane e μ)
      (coeffShift n a) (coeffShift_eq_zero n a N ha) hχH
    -- Mumford's step at `m₀`
    set B := MvPolynomial.eval (coeffShift n a) (mumfordBound n p N)
    set m₀ : ℤ := B ^ 2 + (n + 2 : ℕ)
    have hBm : B ≤ m₀ := by
      have : (0 : ℤ) ≤ ((n + 2 : ℕ) : ℤ) := by positivity
      nlinarith [sq_nonneg (B - 1)]
    have hregH' := IsProjectiveRegular.of_le_of_coherent k ι n e hFH hBm hregH
    have hstep := IsProjectiveRegular.of_hyperplane_euler (hyperplaneSequence μ F) (Iso.refl _) n e
      (hyperplaneSequence_shortExact μ F) hF hFH hregH'
    apply IsProjectiveRegular.of_le_of_coherent k ι n e hF _ hstep
    -- the bound
    have hm₀ : (n + 1 : ℤ) ≤ m₀ - 1 := by
      have : (0 : ℤ) ≤ B ^ 2 := sq_nonneg B
      push_cast [m₀]
      omega
    have hh0 : (projectiveCohomologyDim k ι ((moduleTensorLeftFunctor (ProjectiveSpace k ι)
        (twistingSheaf k ι (m₀ - 1))).obj F) 0 : ℤ) ≤ p * m₀ ^ (n + 1) := by
      have := mono_twistingTensor_map j (m₀ - 1)
      have hle := projectiveCohomologyDim_zero_le_of_mono n e
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (m₀ - 1))).map j)
        (twistingTensor_affineLocallyFiniteType k ι (m₀ - 1) G hG.coherent)
      have hb := hG.dim_le (m₀ - 1) (by omega)
      rw [sub_add_cancel] at hb
      exact (Nat.cast_le.mpr hle).trans hb
    have hχle : -projectiveHilbertFunction k ι F (m₀ - 1) ≤
        ∑ i : Fin (n + 1), a i ^ 2 * (m₀ - 1) ^ (i : ℕ) := by
      rw [hχ]
      apply neg_hilbertSum_le
      · push_cast [Nat.cast_sub (show N + 1 ≤ n + 1 by omega)]
        omega
      · push_cast [Nat.cast_sub (show N + 1 ≤ n + 1 by omega)]
        omega
    rw [eval_mumfordBound_succ]
    have hgoal : m₀ + (projectiveCohomologyDim k ι ((moduleTensorLeftFunctor
        (ProjectiveSpace k ι) (twistingSheaf k ι (m₀ - 1))).obj F) 0 : ℤ) -
        projectiveHilbertFunction k ι F (m₀ - 1) ≤
        m₀ + p * m₀ ^ (n + 1) + ∑ i : Fin (n + 1), a i ^ 2 * (m₀ - 1) ^ (i : ℕ) := by
      linarith
    exact hgoal

/-- **Mumford's bound, conditional on hyperplane sections** (Nitsure, arXiv:math/0504590v1,
Thm 2.3, p. 11): over a field with `HasHyperplaneSections`, for every monomorphism `F ⟶ G` into an
ambient module (for instance `G = O^p`) with `χ(F(r)) = Σ_{i ≤ n} aᵢ C(r, i)` for all `r`, the
module `F` is `mumfordBound n p (n + 1)`-regular at `a`. The bound has integer coefficients and
depends only on `n` and `p`. -/
theorem isProjectiveRegular_mumfordBound_of_hasHyperplaneSections (n p : ℕ)
    (e : ι ≃ Fin (n + 1)) (hgen : HasHyperplaneSections k ι)
    {F G : (ProjectiveSpace k ι).Modules} (j : F ⟶ G)
    [Mono j] (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F)
    (hG : IsMumfordAmbient n p G) (a : Fin (n + 1) → ℤ)
    (hχ : ∀ r : ℤ, projectiveHilbertFunction k ι F r =
      ∑ i : Fin (n + 1), a i * Ring.choose r i) :
    IsProjectiveRegular k ι F (MvPolynomial.eval a (mumfordBound n p (n + 1))) :=
  isProjectiveRegular_mumfordBound_aux n p e hgen (n + 1) le_rfl F G j inferInstance hF hG a
    (fun i hi => absurd hi (by omega)) (fun r => by
      rw [hχ r]
      unfold hilbertSum
      simp)

end Field

end AlgebraicGeometry.Scheme.Cohomology
