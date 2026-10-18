/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Dedekind.AffineEndpointNormEquality

/-! # Actual endpoint norm equality in every degree, including zero -/

@[expose] public noncomputable section
namespace MilnorK.DedekindResidue

open Polynomial PolynomialResidue PolynomialDedekindResidue IsLocalRing IsDedekindDomain
attribute [local instance] Classical.decEq

universe u
variable (k S E : Type u) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S] [Module.Finite k[X] S]
  [Module.IsTorsionFree k[X] S]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E]

attribute [local instance] polynomialPointResidueCharZero
local instance (a : k) : Fact (Irreducible (X - C a)) := ⟨irreducible_X_sub_C a⟩

omit [CharZero k] in
/-- Restriction of constants is surjective in degree zero, through the actual
integer comparison on both fields. -/
theorem constant_restriction_zero_surjective :
    Function.Surjective (MilnorK.map 0 (RatFunc.C : k →+* RatFunc k)) := by
  intro x
  refine ⟨(zeroEquiv k).symm (zeroEquiv (RatFunc k) x), ?_⟩
  apply (zeroEquiv (RatFunc k)).injective
  rw [zeroEquiv_map]
  exact (zeroEquiv k).apply_symm_apply _

/-- Global ring-unit symbols have constant norms in every degree. The zero
case uses the actual integer comparison, not a positive-degree residue premise. -/
theorem norm_ring_unit_symbol_mem_constant_range_all (n : ℕ) (u : Fin n → Sˣ) :
    finiteExtensionNorm (RatFunc k) E n
      (symbol (Units.map (algebraMap S E).toMonoidHom ∘ u)) ∈
      LinearMap.range (MilnorK.map n (RatFunc.C : k →+* RatFunc k)) := by
  cases n with
  | zero => exact constant_restriction_zero_surjective k _
  | succ n => exact norm_ring_unit_symbol_mem_constant_range k S E n u

/-- All literal endpoint specializations agree, including in degree zero. -/
theorem linearSpecialization_norm_ring_unit_symbol_eq_all (a b : k) (n : ℕ)
    (u : Fin n → Sˣ) :
    linearSpecialization a n (finiteExtensionNorm (RatFunc k) E n
      (symbol (Units.map (algebraMap S E).toMonoidHom ∘ u))) =
      linearSpecialization b n (finiteExtensionNorm (RatFunc k) E n
        (symbol (Units.map (algebraMap S E).toMonoidHom ∘ u))) :=
  linearSpecialization_eq_of_mem_constant_range a b n _
    (norm_ring_unit_symbol_mem_constant_range_all k S E n u)

/-- The actual full endpoint sum is the specialization of the original field
norm. Both projection and all-branch residue compatibility are proved inputs. -/
theorem endpointWeightedResidueSum_eq_specialization_all (a : k) (n : ℕ)
    (u : Fin n → Sˣ) :
    endpointWeightedResidueSum k S E a n u =
      linearSpecialization a n (finiteExtensionNorm (RatFunc k) E n
        (symbol (Units.map (algebraMap S E).toMonoidHom ∘ u))) := by
  unfold endpointWeightedResidueSum
  rw [← residueAt_norm_unit_symbol_last k S E (endpointPolynomial k a)]
  have hs := productUnit_symbol n
    (Units.map (algebraMap S E).toMonoidHom ∘ u) (Additive.ofMul (endpointParameter k E a))
  simp only [toMul_ofMul] at hs
  rw [← hs]
  change linearResidue a n
    (finiteExtensionNorm (RatFunc k) E (n + 1)
      (productUnit n (symbol (Units.map (algebraMap S E).toMonoidHom ∘ u))
        (MilnorK.K2.unitsLinear (algebraMap (RatFunc k) E)
          (Additive.ofMul (polynomialUnit (X - C a) (irreducible_X_sub_C a).ne_zero))))) = _
  rw [finiteExtensionNorm_productUnit_constants_right]
  exact linearResidue_productUnit_eq_specialization a n _
    (norm_ring_unit_symbol_mem_constant_range_all k S E n u)

/-- Any two actual endpoint branch sums agree, with every branch and its full
order retained. No endpoint-boundary compatibility is assumed. -/
theorem endpointWeightedResidueSum_eq_all (a b : k) (n : ℕ) (u : Fin n → Sˣ) :
    endpointWeightedResidueSum k S E a n u =
      endpointWeightedResidueSum k S E b n u := by
  rw [endpointWeightedResidueSum_eq_specialization_all,
    endpointWeightedResidueSum_eq_specialization_all]
  exact linearSpecialization_norm_ring_unit_symbol_eq_all k S E a b n u

end MilnorK.DedekindResidue
