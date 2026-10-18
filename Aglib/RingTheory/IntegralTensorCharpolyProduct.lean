/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.TensorCharpolyProduct
public import Aglib.RingTheory.DVRCharpolyResidue

/-!
# Characteristic-polynomial products for actual integral tensor models

The actual integral multiplication operators are compared in the fraction field.
Their characteristic polynomials are identified there by the literal tensor
algebra equivalence, and injectivity descends the equality to the integral base.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra

/-- An actual tensor decomposition identifies the multiplication characteristic
polynomials of compatible elements in the actual integral closures. No integral
product identity or ramification count is assumed. -/
theorem map_charpoly_lmul_eq_prod_integralClosure
    (R F S E T L : Type*)
    [CommRing R] [IsDomain R] [Field F] [CommRing S] [Field E]
    [Algebra R F] [IsFractionRing R F] [Algebra R S] [Algebra F E]
    [Algebra R E] [Algebra S E] [IsScalarTower R F E] [IsScalarTower R S E]
    [IsIntegralClosure S R E] [FiniteDimensional F E]
    [Module.Free R S] [Module.Finite R S]
    [CommRing T] [IsDomain T] [Field L] [Algebra R T] [Algebra T L]
    [IsFractionRing T L] [Algebra F L] [Algebra R L]
    [IsScalarTower R T L] [IsScalarTower R F L]
    {ι : Type*} [Fintype ι] (D U : ι → Type*)
    [∀ i, Field (D i)] [∀ i, CommRing (U i)]
    [∀ i, Algebra L (D i)] [∀ i, Algebra T (U i)]
    [∀ i, Algebra T (D i)] [∀ i, Algebra (U i) (D i)]
    [∀ i, IsScalarTower T L (D i)] [∀ i, IsScalarTower T (U i) (D i)]
    [∀ i, IsIntegralClosure (U i) T (D i)] [∀ i, FiniteDimensional L (D i)]
    [∀ i, Module.Free T (U i)] [∀ i, Module.Finite T (U i)]
    (ε : (L ⊗[F] E) ≃ₐ[L] (∀ i, D i)) (b : S) (c : ∀ i, U i)
    (hc : ∀ i, algebraMap (U i) (D i) (c i) =
      ε (1 ⊗ₜ[F] (algebraMap S E b)) i) :
    ((lmul R S b).charpoly).map (algebraMap R T) =
      ∏ i, (lmul T (U i) (c i)).charpoly := by
  apply Polynomial.map_injective (algebraMap T L) (IsFractionRing.injective T L)
  have hmap : (algebraMap T L).comp (algebraMap R T) =
      (algebraMap F L).comp (algebraMap R F) := by
    ext r
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R T L,
      ← IsScalarTower.algebraMap_apply R F L]
  rw [Polynomial.map_map, hmap, ← Polynomial.map_map,
    map_charpoly_lmul_integralClosure R F S E b,
    map_charpoly_lmul_eq_prod_tensor D ε]
  rw [Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_charpoly_lmul_integralClosure T L (U i) (D i) (c i), hc i]

end Algebra
