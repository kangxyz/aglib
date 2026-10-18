/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Mumford.InfiniteField
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Mumford.FieldExtension
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Mumford's bound over an arbitrary field

Nitsure, arXiv:math/0504590v1, Thm 2.3 (statement p. 11, proof pp. 12-13): for all `n p : ℕ`
there is an integer polynomial `F_{p,n}` in `n + 1` variables such that over every field `k`,
every coherent submodule `F` of `O^p` on `P^n_k` with `χ(F(r)) = Σ_{i ≤ n} aᵢ C(r, i)` is
`F_{p,n}(a)`-regular. Here `F_{p,n} = mumfordBound n p (n + 1)`, and the theorem holds with no
premise (`isProjectiveRegular_mumfordBound_free`; the case `p = 1` of ideal sheaves is
`isProjectiveRegular_mumfordBound_ideal`). The coefficients `aᵢ` always exist
(`exists_projectiveHilbertFunction_eq_sum_choose`), so every coherent submodule of `O^p` is
`F_{p,n}(a)`-regular for its own Hilbert coefficients `a`
(`exists_isProjectiveRegular_mumfordBound_free`).

As in Nitsure (p. 12, "as before, we can assume that `k` is infinite"), the proof passes to the
algebraic closure `K` of `k`, which is infinite: hyperplane sections exist over `K`
(`hasHyperplaneSections_of_infinite`), and `isProjectiveRegular_mumfordBound_free_of_extension`
descends the bound from `P^n_K` to `P^n_k`, with the twisting sheaves pulled back by
`ProjectiveSpace.twistingPullbackIso`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {k : Type u} [Field k] {ι : Type u}

/-- **Mumford's bound** (Nitsure, arXiv:math/0504590v1, Thm 2.3, p. 11): over every field `k`,
if `F` is a coherent submodule of `O^p = ∐_{i < p} O(0)` on `P^n_k` with
`χ(F(r)) = Σ_{i ≤ n} aᵢ C(r, i)` for all `r : ℤ`, then `F` is `F_{p,n}(a)`-regular for the
integer polynomial `F_{p,n} = mumfordBound n p (n + 1)`, which depends only on `n` and `p`. -/
theorem isProjectiveRegular_mumfordBound_free (n p : ℕ) (e : ι ≃ Fin (n + 1))
    {F : (ProjectiveSpace k ι).Modules}
    (j : F ⟶ ∐ fun _ : ULift.{u} (Fin p) => twistingSheaf k ι 0) [Mono j]
    (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F) (a : Fin (n + 1) → ℤ)
    (hχ : ∀ r : ℤ, projectiveHilbertFunction k ι F r =
      ∑ i : Fin (n + 1), a i * Ring.choose r i) :
    IsProjectiveRegular k ι F (MvPolynomial.eval a (mumfordBound n p (n + 1))) :=
  have : Finite ι := Finite.of_equiv _ e.symm
  isProjectiveRegular_mumfordBound_free_of_extension (K := AlgebraicClosure k) n p e
    (hasHyperplaneSections_of_infinite (AlgebraicClosure k) ι) j hF a hχ

/-- **Mumford's bound for ideal sheaves** (Nitsure, arXiv:math/0504590v1, Thm 2.3 with `p = 1`,
the case used for Hilbert schemes): over every field `k`, a coherent submodule `F` of `O = O(0)`
on `P^n_k` with `χ(F(r)) = Σ_{i ≤ n} aᵢ C(r, i)` for all `r : ℤ` is
`mumfordBound n 1 (n + 1)`-regular at `a`. -/
theorem isProjectiveRegular_mumfordBound_ideal (n : ℕ) (e : ι ≃ Fin (n + 1))
    {F : (ProjectiveSpace k ι).Modules} (j : F ⟶ twistingSheaf k ι 0) [Mono j]
    (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F) (a : Fin (n + 1) → ℤ)
    (hχ : ∀ r : ℤ, projectiveHilbertFunction k ι F r =
      ∑ i : Fin (n + 1), a i * Ring.choose r i) :
    IsProjectiveRegular k ι F (MvPolynomial.eval a (mumfordBound n 1 (n + 1))) :=
  isProjectiveRegular_mumfordBound_free n 1 e
    (j ≫ (coproductUniqueIso fun _ : ULift.{u} (Fin 1) => twistingSheaf k ι 0).inv) hF a hχ

/-- **Mumford's bound with its Hilbert coefficients**: over every field `k`, a coherent
submodule `F` of `O^p` on `P^n_k` has integers `a₀, …, aₙ` with `χ(F(r)) = Σ_{i ≤ n} aᵢ C(r, i)`
for all `r : ℤ`, and `F` is `F_{p,n}(a)`-regular for these `a`. -/
theorem exists_isProjectiveRegular_mumfordBound_free (n p : ℕ) (e : ι ≃ Fin (n + 1))
    {F : (ProjectiveSpace k ι).Modules}
    (j : F ⟶ ∐ fun _ : ULift.{u} (Fin p) => twistingSheaf k ι 0) [Mono j]
    (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F) :
    ∃ a : Fin (n + 1) → ℤ, (∀ r : ℤ, projectiveHilbertFunction k ι F r =
      ∑ i : Fin (n + 1), a i * Ring.choose r i) ∧
      IsProjectiveRegular k ι F (MvPolynomial.eval a (mumfordBound n p (n + 1))) := by
  obtain ⟨a, ha⟩ := exists_projectiveHilbertFunction_eq_sum_choose k ι n e F hF
  exact ⟨a, ha, isProjectiveRegular_mumfordBound_free n p e j hF a ha⟩

end AlgebraicGeometry.Scheme.Cohomology
