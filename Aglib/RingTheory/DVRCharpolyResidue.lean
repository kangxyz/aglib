/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DVRNormResidueUnit
public import Aglib.FieldTheory.FieldCharpolyPower
public import Mathlib.RingTheory.Localization.NormTrace
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-!
# Reduction of the actual multiplication characteristic polynomial over a DVR

The finite free integral algebra retains its literal multiplication operator.
Evaluation of its characteristic polynomial is the determinant norm of a
scalar translate. The proved closed-fiber norm formula therefore yields the
residue characteristic polynomial with its full ramification exponent.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

namespace Algebra

/-- Evaluating the original multiplication characteristic polynomial is the
norm of the literal scalar translate, with no separability assumption. -/
theorem eval_charpoly_lmul_eq_norm
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S] (b : S) (r : R) :
    (Algebra.lmul R S b).charpoly.eval r =
      Algebra.norm R (algebraMap R S r - b) := by
  rw [LinearMap.eval_charpoly, Algebra.norm_apply]
  congr 1
  ext x
  change r • x - b * x = (algebraMap R S r - b) * x
  rw [Algebra.smul_def, sub_mul]

/-- The original integral multiplication characteristic polynomial becomes the
original field multiplication characteristic polynomial, using the actual
integral-closure localization and the given scalar towers. -/
theorem map_charpoly_lmul_integralClosure
    (R F S E : Type*) [CommRing R] [IsDomain R] [Field F]
    [CommRing S] [Field E] [Algebra R F] [IsFractionRing R F]
    [Algebra R S] [Algebra F E] [Algebra R E] [Algebra S E]
    [IsScalarTower R F E] [IsScalarTower R S E] [IsIntegralClosure S R E]
    [FiniteDimensional F E] [Module.Free R S] [Module.Finite R S] (b : S) :
    (Algebra.lmul R S b).charpoly.map (algebraMap R F) =
      (Algebra.lmul F E (algebraMap S E b)).charpoly := by
  classical
  let : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) E :=
    IsIntegralClosure.isLocalization R F E S
  let B := Module.Free.chooseBasis R S
  rw [← LinearMap.charpoly_toMatrix _ B,
    ← LinearMap.charpoly_toMatrix _ (B.localizationLocalization F (nonZeroDivisors R) E)]
  change (leftMulMatrix B b).charpoly.map (algebraMap R F) =
    (leftMulMatrix (B.localizationLocalization F (nonZeroDivisors R) E)
      (algebraMap S E b)).charpoly
  rw [← Matrix.charpoly_map]
  congr 1
  exact Algebra.map_leftMulMatrix_localization R (nonZeroDivisors R) B b

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S] [IsLocalHom (algebraMap R S)]
  [Infinite (ResidueField R)]

/-- Reduction of the literal integral multiplication characteristic polynomial
is the residue multiplication characteristic polynomial to the actual
uniformizer exponent. The infinite residue field is only used for polynomial
extensionality; in particular characteristic-zero residue fields qualify. -/
theorem residue_charpoly_lmul_eq_pow
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) (b : S) :
    (Algebra.lmul R S b).charpoly.map (residue R) =
      (Algebra.lmul (ResidueField R) (ResidueField S) (residue S b)).charpoly ^ e := by
  apply Polynomial.funext
  intro a
  obtain ⟨r, rfl⟩ := residue_surjective a
  rw [Polynomial.eval_map_apply, Polynomial.eval_pow,
    eval_charpoly_lmul_eq_norm, eval_charpoly_lmul_eq_norm]
  have hn := residue_intNorm_eq_norm_residue_pow R S hπ hϖ u e he
    (algebraMap R S r - b)
  rw [Algebra.intNorm_eq_norm] at hn
  simpa only [map_sub, ResidueField.algebraMap_residue] using hn

/-- The reduction is a power of the minimal polynomial of the actual residue
class. Its exponent retains both ramification and the relative residue degree. -/
theorem residue_charpoly_lmul_eq_minpoly_pow
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) (b : S) :
    (Algebra.lmul R S b).charpoly.map (residue R) =
      (minpoly (ResidueField R) (residue S b)) ^
        (e * Module.finrank
          (IntermediateField.adjoin (ResidueField R) {residue S b}) (ResidueField S)) := by
  rw [residue_charpoly_lmul_eq_pow R S hπ hϖ u e he b,
    charpoly_lmul_eq_minpoly_pow, ← pow_mul, Nat.mul_comm]

/-- If the residue of the chosen integral element is the generator of an actual
power basis, the full reduction exponent is exactly the ramification index. -/
theorem residue_charpoly_lmul_eq_minpoly_pow_of_powerBasis
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) (b : S)
    (B : PowerBasis (ResidueField R) (ResidueField S)) (hB : B.gen = residue S b) :
    (Algebra.lmul R S b).charpoly.map (residue R) =
      (minpoly (ResidueField R) (residue S b)) ^ e := by
  rw [residue_charpoly_lmul_eq_pow R S hπ hϖ u e he b, ← hB]
  congr 1
  rw [← LinearMap.charpoly_toMatrix _ B.basis]
  exact charpoly_leftMulMatrix B

end Algebra
