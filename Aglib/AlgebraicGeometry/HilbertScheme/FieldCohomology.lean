/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.QuotientDirectImage

/-!
# Cohomology of the twisted ideal and structure sheaves of a subscheme over a field

Let `k` be a field, `ι ≃ Fin (n + 1)` and `W ⊆ P^n_k` a closed subscheme with Hilbert polynomial
`Φ`. The ideal sheaf `I_W` is `m`-regular for `m = hilbertRegularityBound n Φ` (Mumford's bound,
`isProjectiveRegular_idealModule`), so for `r ≥ m` the higher cohomology of `I_W(r)` and of
`𝒪_W(r)` vanishes (the vanishing half of Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, Lemma 2.1 (c), p. 10, with the sequence `0 → I_W → 𝒪 → 𝒪_W → 0`), and the
Euler characteristics give the dimensions of the global sections:

* `projectiveCohomologyDim_quotientTwist_zero_cast`: `h^0(𝒪_W(r)) = Φ(r)` (as rational numbers;
  in particular `Φ(r)` is a natural number);
* `projectiveCohomologyDim_idealTwist_zero_cast`: `h^0(I_W(r)) = C(r + n, n) - Φ(r)`;
* `projectiveCohomologyDim_idealTwist_zero`: `h^0(I_W(r)) = C(n + r, r) - ⌊Φ(r)⌋₊`;
* `subsingleton_moduleCohomology_quotientTwist_of_field`: `H^q(𝒪_W(r)) = 0` for `q ≥ 1`.

These are the fibre inputs of (*) and (**) of Nitsure, §5, p. 25, "Use of m-Regularity", for
`𝒪_Z(r)` (`HilbertScheme/DirectImageSheaf`) and `I_Z(r)` (`HilbertScheme/IdealTwist/Fiber`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Polynomial

universe u

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Cohomology Scheme.Modules.QuasiCoherent

variable (ι : Type u)

section Field


variable {k : Type u} [Field k] (n : ℕ) (e : ι ≃ Fin (n + 1))
  (W : (ProjectiveSpace k ι).IdealSheafData) {Φ : ℚ[X]}

include e in
/-- **`h^0` of the twisted ideal sheaf over a field**, as a rational number: for `W ⊆ P^n_k` with
Hilbert polynomial `Φ` and a natural `r ≥ hilbertRegularityBound n Φ`,
`h^0(I_W(r)) = C(r + n, n) - Φ(r)`, since the higher cohomology vanishes by regularity. -/
theorem projectiveCohomologyDim_idealTwist_zero_cast (hW : subschemeHilbertPolynomial ι k W = Φ)
    (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) :
    (projectiveCohomologyDim k ι (idealTwist ι W r) 0 : ℚ) =
      ((r + n).choose n : ℚ) - Φ.eval (r : ℚ) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have hreg := isProjectiveRegular_idealModule ι n e W
  rw [hW] at hreg
  have hI := Scheme.Hom.affineLocallyFiniteType_idealModule W.subschemeι
  have hχ := projectiveHilbertFunction_idealModule ι n e W r
  rw [hW] at hχ
  rw [← hχ]
  have hM : affineLocallyFiniteType _ (idealTwist ι W r) :=
    twistingTensor_affineLocallyFiniteType k ι r _ hI
  have : (idealTwist ι W r).IsQuasicoherent :=
    quasicoherent_of_affineCharts _ (fun R j _ => (hM R j).1)
  change _ = ((projectiveEulerChar k ι (idealTwist ι W r) : ℤ) : ℚ)
  rw [projectiveEulerChar_eq_sum_range k ι n e (idealTwist ι W r), Finset.sum_range_succ']
  have hpos (q : ℕ) : projectiveCohomologyDim k ι (idealTwist ι W r) (q + 1) = 0 :=
    projectiveCohomologyDim_eq_zero_of_subsingleton
      (IsProjectiveRegular.cohomology_subsingleton_of_le_of_coherent k ι n e hI hreg hr
        (Nat.succ_pos q))
  simp only [hpos, CharP.cast_eq_zero, mul_zero, Finset.sum_const_zero, zero_add, pow_zero,
    one_mul, Int.cast_natCast]

include e in
/-- **`h^0` of the twisted structure sheaf over a field**: for `W ⊆ P^n_k` with Hilbert polynomial
`Φ` and a natural `r ≥ hilbertRegularityBound n Φ`, `h^0(𝒪_W(r)) = Φ(r)`; in particular `Φ(r)`
is a natural number. -/
theorem projectiveCohomologyDim_quotientTwist_zero_cast
    (hW : subschemeHilbertPolynomial ι k W = Φ) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) :
    (projectiveCohomologyDim k ι (quotientTwist ι W r) 0 : ℚ) = Φ.eval (r : ℚ) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have hreg := isProjectiveRegular_idealModule ι n e W
  rw [hW] at hreg
  have hQ := W.affineLocallyFiniteType_quotientModule
  have hχ := projectiveHilbertFunction_eq_eval k ι n e _ hQ r
  have hP : projectiveHilbertPolynomial k ι W.quotientModule = Φ := hW
  rw [hP, Int.cast_natCast] at hχ
  rw [← hχ]
  have hM : affineLocallyFiniteType _ (quotientTwist ι W r) :=
    twistingTensor_affineLocallyFiniteType k ι r _ hQ
  have : (quotientTwist ι W r).IsQuasicoherent :=
    quasicoherent_of_affineCharts _ (fun R j _ => (hM R j).1)
  change _ = ((projectiveEulerChar k ι (quotientTwist ι W r) : ℤ) : ℚ)
  rw [projectiveEulerChar_eq_sum_range k ι n e (quotientTwist ι W r), Finset.sum_range_succ']
  have hpos (q : ℕ) : projectiveCohomologyDim k ι (quotientTwist ι W r) (q + 1) = 0 :=
    projectiveCohomologyDim_eq_zero_of_subsingleton
      (subsingleton_moduleCohomology_quotientTwist_of_isProjectiveRegular ι n e W hreg hr
        (by omega) (q + 1) (Nat.succ_ne_zero q))
  simp only [hpos, CharP.cast_eq_zero, mul_zero, Finset.sum_const_zero, zero_add, pow_zero,
    one_mul, Int.cast_natCast]

include e in
/-- **`h^0` of the twisted ideal sheaf over a field**: for `W ⊆ P^n_k` with Hilbert polynomial
`Φ` and a natural `r ≥ hilbertRegularityBound n Φ`, `h^0(I_W(r)) = C(n + r, r) - ⌊Φ(r)⌋₊`, the
rank of the kernel of `k[x]_r ↠ H^0(𝒪_W(r))`. -/
theorem projectiveCohomologyDim_idealTwist_zero (hW : subschemeHilbertPolynomial ι k W = Φ)
    (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) :
    projectiveCohomologyDim k ι (idealTwist ι W r) 0 = (n + r).choose r - ⌊Φ.eval (r : ℚ)⌋₊ := by
  have hI := projectiveCohomologyDim_idealTwist_zero_cast ι n e W hW r hr
  have hQ := projectiveCohomologyDim_quotientTwist_zero_cast ι n e W hW r hr
  have hc : (r + n).choose n = (n + r).choose r := by rw [Nat.add_comm r n, Nat.choose_symm_add]
  rw [hc] at hI
  rw [← hQ, Nat.floor_natCast]
  have h : ((projectiveCohomologyDim k ι (idealTwist ι W r) 0 +
      projectiveCohomologyDim k ι (quotientTwist ι W r) 0 : ℕ) : ℚ) = ((n + r).choose r : ℚ) := by
    rw [Nat.cast_add]
    linarith
  have h' : projectiveCohomologyDim k ι (idealTwist ι W r) 0 +
      projectiveCohomologyDim k ι (quotientTwist ι W r) 0 = (n + r).choose r := by
    exact_mod_cast h
  omega

end Field

section Vanishing

variable (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]}

include e in
/-- **Vanishing of the higher cohomology of `𝒪_W(r)` over a field**: for `W ⊆ P^n_k` with Hilbert
polynomial `Φ` and `r ≥ hilbertRegularityBound n Φ`, `H^q(P^n_k, 𝒪_W(r)) = 0` for `q ≥ 1`. -/
theorem subsingleton_moduleCohomology_quotientTwist_of_field (k : Type u) [Field k]
    (W : (ProjectiveSpace k ι).IdealSheafData) (hW : subschemeHilbertPolynomial ι k W = Φ)
    (r : ℤ) (hr : hilbertRegularityBound n Φ ≤ r) (q : ℕ) (hq : q ≠ 0) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace k ι) (quotientTwist ι W r))
      q) := by
  have hreg := isProjectiveRegular_idealModule ι n e W
  rw [hW] at hreg
  have hr' : -(n : ℤ) ≤ r := by have := add_two_le_hilbertRegularityBound n Φ; omega
  exact subsingleton_moduleCohomology_quotientTwist_of_isProjectiveRegular ι n e W hreg hr hr' q hq

end Vanishing

end AlgebraicGeometry.ProjectiveSpace
