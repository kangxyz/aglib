/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Functor
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Mumford.ArbitraryField
public import Aglib.AlgebraicGeometry.Cohomology.Projective.GlobalSections.Polynomial
public import Aglib.AlgebraicGeometry.Cohomology.Projective.TwistCohomology
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Basic
public import Aglib.RingTheory.Binomial.Uniqueness
public import Aglib.RingTheory.MvPolynomial.HomogeneousFinrank

/-!
# A uniform regularity bound for the fibers of the Hilbert functor

Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 25: for `n` and
`Φ` there is an integer `m`, depending only on `n` and `Φ`, such that the ideal sheaf of every
closed subscheme `W ⊆ P^n_k` over a field `k` with Hilbert polynomial `Φ` is `m`-regular. This is
Mumford's bound (Thm 2.3, `isProjectiveRegular_mumfordBound_ideal`, the case `p = 1`) applied to
`I_W ⊆ 𝒪 ≅ 𝒪(0)`, whose Hilbert function is `r ↦ C(r + n, n) - Φ(r)`.

* `projectiveHilbertFunction_unit`: `χ(𝒪(r)) = C(r + n, n)` on `P^n_k` for `r ≥ 0`, from
  `H^0(𝒪(r)) ≅ k[x]_r` (`twistingH0PolynomialLinearEquiv`, of dimension
  `MvPolynomial.finrank_homogeneousSubmodule_eq`) and the vanishing of the higher cohomology
  (`twistingCohomology_subsingleton_of_neg_le_degree`).
* `hilbertRegularityBound n Φ`: Mumford's bound `mumfordBound n 1 (n + 1)` evaluated at the
  binomial coefficients of `r ↦ C(r + n, n) - Φ(r)` (unique by
  `Int.eq_of_forall_sum_mul_choose_eq`); an integer depending only on `n` and `Φ`, at least
  `n + 2` (`add_two_le_hilbertRegularityBound`).
* `isProjectiveRegular_idealModule`: the ideal sheaf of a closed subscheme `W ⊆ P^n_k` is
  `hilbertRegularityBound n Φ`-regular for `Φ` its Hilbert polynomial, over every field `k`.
* `IsHilbertFamily.isProjectiveRegular_fiber`: for every point `Z` of the Hilbert functor over any
  `T` and every field point `x` of `T`, the ideal sheaf of the fiber `Z_x ⊆ P^n_K` is
  `hilbertRegularityBound n Φ`-regular.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped Polynomial

universe u

namespace AlgebraicGeometry

namespace Scheme.Cohomology

open ProjectiveSpace

variable (ι : Type u) (k : Type u) [Field k]

/-- **The Hilbert function of `𝒪` on `P^n_k`**: `χ(𝒪(r)) = C(r + n, n)` for every `r ≥ 0`. The
higher cohomology of `𝒪(r)` vanishes (`r ≥ -n`), and `H^0(𝒪(r))` is the space of homogeneous
polynomials of degree `r` in `n + 1` variables. -/
theorem projectiveHilbertFunction_unit (n : ℕ) (e : ι ≃ Fin (n + 1)) (r : ℕ) :
    projectiveHilbertFunction k ι (SheafOfModules.unit (ProjectiveSpace k ι).ringCatSheaf) r =
      ((r + n).choose n : ℤ) := by
  let := Fintype.ofEquiv (Fin (n + 1)) e.symm
  have : Finite ι := Finite.of_equiv _ e.symm
  let O := SheafOfModules.unit (ProjectiveSpace k ι).ringCatSheaf
  let M := (moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι r)).obj O
  have hM : affineLocallyFiniteType (ProjectiveSpace k ι) M :=
    twistingTensor_affineLocallyFiniteType k ι r O
      (Scheme.Modules.affineLocallyFiniteType_unit _)
  have : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun R j _ => (hM R j).1)
  let ρ : M ≅ twistingSheaf k ι r := ρ_ (twistingSheaf k ι r)
  change projectiveEulerChar k ι M = _
  rw [projectiveEulerChar_eq_sum_range k ι n e M, Finset.sum_range_succ']
  have hpos (q : ℕ) : projectiveCohomologyDim k ι M (q + 1) = 0 := by
    rw [projectiveCohomologyDim_congr k ι ρ]
    exact projectiveCohomologyDim_eq_zero_of_subsingleton
      (twistingCohomology_subsingleton_of_neg_le_degree k ι n e r (q + 1) (by omega)
        (Nat.succ_ne_zero q))
  have h0 : projectiveCohomologyDim k ι M 0 = (r + n).choose n := by
    rw [projectiveCohomologyDim_congr k ι ρ]
    let := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) (projectiveConstants k ι)
      (twistingSheaf k ι (r : ℤ)) 0
    have h := (twistingH0PolynomialLinearEquiv k ι (e.symm 0) r).finrank_eq
    rw [MvPolynomial.finrank_homogeneousSubmodule_eq, Fintype.card_congr e, Fintype.card_fin,
      show n + 1 + r - 1 = r + n by omega, Nat.choose_symm_add] at h
    exact h
  simp only [hpos, h0, CharP.cast_eq_zero, mul_zero, Finset.sum_const_zero, zero_add, pow_zero,
    one_mul]

end Scheme.Cohomology

namespace ProjectiveSpace

open Scheme.Cohomology

variable (ι : Type u)

/-- The binomial coefficients `a` of the Hilbert function `r ↦ C(r + n, n) - Φ(r)` of the ideal
sheaf of a closed subscheme of `P^n` with Hilbert polynomial `Φ`, written
`Σ_{i ≤ n} aᵢ C(r, i)` for natural `r`; `0` when there are none. By
`Int.eq_of_forall_sum_mul_choose_eq` they are unique when they exist. -/
def idealHilbertCoeffs (n : ℕ) (Φ : ℚ[X]) : Fin (n + 1) → ℤ := by
  classical
  exact if h : ∃ a : Fin (n + 1) → ℤ, ∀ r : ℕ,
      ((∑ i, a i * Ring.choose (r : ℤ) i : ℤ) : ℚ) = ((r + n).choose n : ℚ) - Φ.eval (r : ℚ)
    then h.choose else 0

theorem idealHilbertCoeffs_eq (n : ℕ) (Φ : ℚ[X]) (a : Fin (n + 1) → ℤ)
    (ha : ∀ r : ℕ, ((∑ i, a i * Ring.choose (r : ℤ) i : ℤ) : ℚ) =
      ((r + n).choose n : ℚ) - Φ.eval (r : ℚ)) :
    idealHilbertCoeffs n Φ = a := by
  have h : ∃ a : Fin (n + 1) → ℤ, ∀ r : ℕ,
      ((∑ i, a i * Ring.choose (r : ℤ) i : ℤ) : ℚ) = ((r + n).choose n : ℚ) - Φ.eval (r : ℚ) :=
    ⟨a, ha⟩
  unfold idealHilbertCoeffs
  rw [dite_eq_left h]
  exact Int.eq_of_forall_sum_mul_choose_eq fun r =>
    Int.cast_injective (α := ℚ) ((h.choose_spec r).trans (ha r).symm)

/-- **The uniform regularity bound** of the Hilbert functor `Hilb^Φ` of `P^n` (Nitsure,
arXiv:math/0504590v1, §5, p. 25): Mumford's bound `mumfordBound n 1 (n + 1)` (Thm 2.3 with `p = 1`)
at the binomial coefficients of `r ↦ C(r + n, n) - Φ(r)`. It depends only on `n` and `Φ`. -/
def hilbertRegularityBound (n : ℕ) (Φ : ℚ[X]) : ℤ :=
  MvPolynomial.eval (idealHilbertCoeffs n Φ) (mumfordBound n 1 (n + 1))

/-- **The uniform regularity bound is at least `n + 2`**: in Mumford's recursion
(`eval_mumfordBound_succ`) the first summand is at least `n + 2` and the other two are
nonnegative. In particular every `r ≥ hilbertRegularityBound n Φ` satisfies `r ≥ -n`. -/
theorem add_two_le_hilbertRegularityBound (n : ℕ) (Φ : ℚ[X]) :
    (n : ℤ) + 2 ≤ hilbertRegularityBound n Φ := by
  unfold hilbertRegularityBound
  rw [eval_mumfordBound_succ]
  set x := MvPolynomial.eval (coeffShift n (idealHilbertCoeffs n Φ)) (mumfordBound n 1 n)
  have h1 : (0 : ℤ) ≤ x ^ 2 := sq_nonneg x
  have h2 : (0 : ℤ) ≤ ((1 : ℕ) : ℤ) * (x ^ 2 + ((n + 2 : ℕ) : ℤ)) ^ (n + 1) := by positivity
  have h3 : (0 : ℤ) ≤ ∑ i : Fin (n + 1), idealHilbertCoeffs n Φ i ^ 2 *
      (x ^ 2 + ((n + 2 : ℕ) : ℤ) - 1) ^ (i : ℕ) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _)
      (pow_nonneg (by push_cast; linarith) _)
  push_cast at h2 h3 ⊢
  linarith

variable {k : Type u} [Field k]

/-- **The Hilbert function of the ideal sheaf**: for a closed subscheme `W ⊆ P^n_k` with Hilbert
polynomial `Φ`, `χ(I_W(r)) = C(r + n, n) - Φ(r)` for every `r ≥ 0`, by additivity on
`0 → I_W → 𝒪 → 𝒪_W → 0`. -/
theorem projectiveHilbertFunction_idealModule (n : ℕ) (e : ι ≃ Fin (n + 1))
    (W : (ProjectiveSpace k ι).IdealSheafData) (r : ℕ) :
    (projectiveHilbertFunction k ι (Scheme.Hom.idealModule W.subschemeι) r : ℚ) =
      ((r + n).choose n : ℚ) - (subschemeHilbertPolynomial ι k W).eval (r : ℚ) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have hI := Scheme.Hom.affineLocallyFiniteType_idealModule W.subschemeι
  have hO := Scheme.Modules.affineLocallyFiniteType_unit (ProjectiveSpace k ι)
  have hW := W.affineLocallyFiniteType_quotientModule
  have hadd := projectiveHilbertPolynomial_add_of_shortExact k ι n e W.shortComplex
    W.shortComplex_shortExact hI hO hW
  have hev : (projectiveHilbertPolynomial k ι
        (SheafOfModules.unit (ProjectiveSpace k ι).ringCatSheaf)).eval ((r : ℤ) : ℚ) =
      (projectiveHilbertPolynomial k ι (Scheme.Hom.idealModule W.subschemeι)).eval
          ((r : ℤ) : ℚ) +
        (projectiveHilbertPolynomial k ι W.quotientModule).eval ((r : ℤ) : ℚ) := by
    have h' := congrArg (fun P : ℚ[X] => P.eval ((r : ℤ) : ℚ)) hadd
    simp only [Polynomial.eval_add] at h'
    exact h'
  have hO' := projectiveHilbertFunction_eq_eval k ι n e _ hO r
  have hr : ((r : ℤ) : ℚ) = (r : ℚ) := Int.cast_natCast r
  rw [projectiveHilbertFunction_eq_eval k ι n e _ hI r, subschemeHilbertPolynomial, ← hr,
    eq_sub_iff_add_eq, ← hev, ← hO', projectiveHilbertFunction_unit ι k n e r]
  push_cast
  ring

/-- **Mumford's bound for subschemes**: over every field `k`, the ideal sheaf of a closed subscheme
`W ⊆ P^n_k` is `hilbertRegularityBound n Φ`-regular, for `Φ` the Hilbert polynomial of `W`. -/
theorem isProjectiveRegular_idealModule (n : ℕ) (e : ι ≃ Fin (n + 1))
    (W : (ProjectiveSpace k ι).IdealSheafData) :
    IsProjectiveRegular k ι (Scheme.Hom.idealModule W.subschemeι)
      (hilbertRegularityBound n (subschemeHilbertPolynomial ι k W)) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have hI := Scheme.Hom.affineLocallyFiniteType_idealModule W.subschemeι
  obtain ⟨a, ha⟩ := exists_projectiveHilbertFunction_eq_sum_choose k ι n e _ hI
  have hcoeff : idealHilbertCoeffs n (subschemeHilbertPolynomial ι k W) = a :=
    idealHilbertCoeffs_eq n _ a fun r => by
      rw [← projectiveHilbertFunction_idealModule ι n e W r, ha r]
  unfold hilbertRegularityBound
  rw [hcoeff]
  exact isProjectiveRegular_mumfordBound_ideal n e
    (Scheme.Hom.idealInclusion W.subschemeι ≫ (twistingZeroIso k ι).inv) hI a ha

/-- **The uniform regularity bound for the Hilbert functor** (Nitsure, arXiv:math/0504590v1, §5,
p. 25): for every scheme `T` over `Spec A`, every point `Z` of `Hilb^Φ(T)` and every field point
`x : Spec K ⟶ T`, the ideal sheaf of the fiber `Z_x ⊆ P^n_K` is `m`-regular for
`m = hilbertRegularityBound n Φ`, which depends only on `n` and `Φ`. -/
theorem IsHilbertFamily.isProjectiveRegular_fiber {A : Type u} [CommRing A] (n : ℕ)
    (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]} {T : Scheme.{u}} {g : T ⟶ Spec (CommRingCat.of A)}
    {Z : (pullback (toSpec A ι) g).IdealSheafData} (hZ : IsHilbertFamily ι Φ g Z)
    (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ T) :
    IsProjectiveRegular K ι (Scheme.Hom.idealModule (Z.comap (pointMap ι g x)).subschemeι)
      (hilbertRegularityBound n Φ) := by
  have h := isProjectiveRegular_idealModule ι n e (Z.comap (pointMap ι g x))
  rwa [hZ.subschemeHilbertPolynomial_fiber K x] at h

end ProjectiveSpace

end AlgebraicGeometry
