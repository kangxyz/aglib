/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Difference
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.TwistMultiplication
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Basic

/-! Focused consumer of the Hilbert-polynomial inputs: integer functions given by rational
polynomials, and multiplication by global twist sections on actual tensor twists of
`ProjectiveSpace R ι` (arbitrary commutative `R`, coordinate type `ι : Type u`). -/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent Polynomial

universe u

example (f : ℤ → ℤ) (h : Polynomial.IsPolynomialOnInt fun m => f (m + 1) - f m) :
    Polynomial.IsPolynomialOnInt f :=
  h.of_fwdDiff

example (R : Type u) [CommRing R] (ι : Type u) (a d e : ℤ)
    (s : (twistingSheaf R ι a).val.obj (op ⊤)) (F : (ProjectiveSpace R ι).Modules)
    (hF : (twistingTensorMultiply R ι a d s).app F = 0) :
    (twistingTensorMultiply R ι a e s).app
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F) = 0 :=
  twistingTensorMultiply_app_tensor_eq_zero R ι a d e s F hF

/-- The Euler characteristic is the alternating sum of the dimensions of the original
`Sheaf.H`, with the structural `k`-action through `toSpec` and `ΓSpecIso`. -/
example (k : Type u) [Field k] (ι : Type u) (M : (ProjectiveSpace k ι).Modules) :
    projectiveEulerChar k ι M =
      ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * (projectiveCohomologyDim k ι M q : ℤ) :=
  rfl

example (k : Type u) [Field k] (ι : Type u) (M : (ProjectiveSpace k ι).Modules) (q : ℕ) :
    projectiveCohomologyDim k ι M q =
      (letI := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) M q
       Module.finrank k (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace k ι) M) q)) :=
  rfl

example (k : Type u) [Field k] (ι : Type u) :
    projectiveConstants k ι =
      (toSpec k ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom :=
  rfl

/-- The Hilbert polynomial of a coherent module on actual projective `n`-space over a field. -/
example (k : Type u) [Field k] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace k ι).Modules) (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F) :
    ∃ Φ : ℚ[X], ∀ m : ℤ, (projectiveEulerChar k ι
      ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι m)).obj F) : ℚ) =
        Φ.eval (m : ℚ) :=
  isPolynomialOnInt_projectiveHilbertFunction k ι n e F hF

/-- The Hilbert polynomial is the unique rational polynomial computing `χ(O(m) ⊗ F)`. -/
example (k : Type u) [Field k] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace k ι).Modules) (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F)
    (Φ : ℚ[X]) :
    (∀ m : ℤ, (projectiveEulerChar k ι
      ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι m)).obj F) : ℚ) =
        Φ.eval (m : ℚ)) ↔ projectiveHilbertPolynomial k ι F = Φ :=
  ⟨projectiveHilbertPolynomial_eq_of_eval k ι F, fun h m => h ▸
    projectiveHilbertFunction_eq_eval k ι n e F hF m⟩

/--
info: 'Polynomial.exists_eval_add_one_sub_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.exists_eval_add_one_sub_eval

/--
info: 'Polynomial.IsPolynomialOnInt.of_fwdDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.IsPolynomialOnInt.of_fwdDiff

/--
info: 'Polynomial.IsPolynomialOnInt.sub' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.IsPolynomialOnInt.sub

/--
info: 'Polynomial.IsPolynomialOnInt.add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.IsPolynomialOnInt.add

/--
info: 'Polynomial.IsPolynomialOnInt.comp_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.IsPolynomialOnInt.comp_add

/--
info: 'AlgebraicGeometry.Scheme.Modules.moduleTensor_nested_hom_ext_of_line' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.moduleTensor_nested_hom_ext_of_line

/--
info: 'AlgebraicGeometry.Scheme.Modules.moduleTensorSection_zero_right' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.moduleTensorSection_zero_right

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingTensorMultiply_section' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingTensorMultiply_section

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingSectionMul_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingSectionMul_swap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.moduleTensorSection_eqToHom_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.moduleTensorSection_eqToHom_eq_zero

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingTensorMultiply_app_tensor_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingTensorMultiply_app_tensor_eq_zero

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isPolynomialOnInt_projectiveHilbertFunction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.isPolynomialOnInt_projectiveHilbertFunction

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isPolynomialOnInt_projectiveHilbertFunction_of_killed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.isPolynomialOnInt_projectiveHilbertFunction_of_killed

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.projectiveEulerChar_add_of_shortExact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.projectiveEulerChar_add_of_shortExact

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.sum_range_alternating_of_long_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.sum_range_alternating_of_long_exact

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.projectiveEulerChar_eq_sum_range' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.projectiveEulerChar_eq_sum_range

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.projectiveEulerChar_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.projectiveEulerChar_congr

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.projectiveEulerChar_of_isZero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.projectiveEulerChar_of_isZero

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isZero_of_coordinate_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isZero_of_coordinate_eq_zero

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsKilledByTwistSection.of_cokernel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsKilledByTwistSection.of_cokernel

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsKilledByTwistSection.of_comp_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsKilledByTwistSection.of_comp_eq_zero

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsKilledByTwistSection.of_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsKilledByTwistSection.of_mono

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsKilledByTwistSection.of_epi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsKilledByTwistSection.of_epi

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsKilledByTwistSection.tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsKilledByTwistSection.tensor

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsKilledByTwistSection.of_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsKilledByTwistSection.of_zero

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingTensor_nested_hom_ext' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingTensor_nested_hom_ext

/--
info: 'AlgebraicGeometry.ProjectiveSpace.coordinateSection_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.coordinateSection_coefficient

/--
info: 'AlgebraicGeometry.Scheme.Modules.moduleTensorSection_smul_left' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.moduleTensorSection_smul_left

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.projectiveHilbertFunction_eq_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.projectiveHilbertFunction_eq_eval

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.projectiveHilbertPolynomial_eq_of_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.projectiveHilbertPolynomial_eq_of_eval

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.projectiveHilbertPolynomial_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.projectiveHilbertPolynomial_congr

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.projectiveHilbertPolynomial_add_of_shortExact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.projectiveHilbertPolynomial_add_of_shortExact

/--
info: 'Polynomial.IsPolynomialOnInt.eq_of_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.IsPolynomialOnInt.eq_of_eval

/--
info: 'Polynomial.IsPolynomialOnInt.polynomialOnInt_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.IsPolynomialOnInt.polynomialOnInt_eq

/-- Integer binomial sums are polynomial on `ℤ`. -/
example (N : ℕ) (a : Fin N → ℤ) :
    Polynomial.IsPolynomialOnInt fun m => ∑ i : Fin N, a i * Ring.choose m i :=
  Polynomial.IsPolynomialOnInt.sum_choose N a

/-- The Hilbert function of a coherent module on `P^n` has integer coefficients `a₀, …, aₙ` in
the binomial basis, the form of the hypothesis of Mumford's bound. -/
example (k : Type u) [Field k] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace k ι).Modules) (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F) :
    ∃ a : Fin (n + 1) → ℤ, ∀ r : ℤ,
      projectiveHilbertFunction k ι F r = ∑ i : Fin (n + 1), a i * Ring.choose r i :=
  exists_projectiveHilbertFunction_eq_sum_choose k ι n e F hF

/--
info: 'Polynomial.IsPolynomialOnInt.sum_choose'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.IsPolynomialOnInt.sum_choose

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_projectiveHilbertFunction_eq_sum_choose_of_killed'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_projectiveHilbertFunction_eq_sum_choose_of_killed

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_projectiveHilbertFunction_eq_sum_choose'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_projectiveHilbertFunction_eq_sum_choose
