/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Dedekind.AffineEndpointResidues
public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.RightProjection

/-! # Equality of actual order-weighted endpoint norm sums -/

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

/-- The literal linear polynomial presenting the original endpoint. -/
abbrev endpointPolynomial (a : k) : MonicIrreducible k :=
  ⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a⟩

/-- The actual parameter unit in the original function field. -/
def endpointParameter (a : k) : Eˣ :=
  Units.map (algebraMap (RatFunc k) E).toMonoidHom
    (polynomialUnit (X - C a) (irreducible_X_sub_C a).ne_zero)

/-- Sum of all original endpoint branch norms, each weighted by its actual
integer order and carrying the literal reduced global coordinate tuple. -/
def endpointWeightedResidueSum (a : k) (n : ℕ) (u : Fin n → Sˣ) : K k n :=
  MilnorK.map n (linearRootEquiv a).toRingHom
    (MilnorK.map n (Polynomial.LocalResidue.residueEquiv (X - C a)).toRingHom
      (∑ q : AdicCompletion.IdealBranch
          ((point (endpointPolynomial k a)).asIdeal.map (algebraMap k[X] S)),
        let Q := branchPoint k[X] S (point (endpointPolynomial k a)) q
        branchCoordinateNorm k[X] S (point (endpointPolynomial k a)) n q
          (MilnorK.K2.DVR.value (Localization.AtPrime Q.asIdeal) E
            (Additive.ofMul (endpointParameter k E a)) •
            symbol (Units.map ((IsLocalRing.residue (Localization.AtPrime Q.asIdeal)).comp
              (algebraMap S (Localization.AtPrime Q.asIdeal))).toMonoidHom ∘ u))))

/-- The actual full endpoint sum is the specialization of the original field
norm. Both projection and all-branch residue compatibility are proved inputs. -/
theorem endpointWeightedResidueSum_eq_specialization (a : k) (n : ℕ)
    (u : Fin (n + 1) → Sˣ) :
    endpointWeightedResidueSum k S E a (n + 1) u =
      linearSpecialization a (n + 1) (finiteExtensionNorm (RatFunc k) E (n + 1)
        (symbol (Units.map (algebraMap S E).toMonoidHom ∘ u))) := by
  unfold endpointWeightedResidueSum
  rw [← residueAt_norm_unit_symbol_last k S E (endpointPolynomial k a)]
  have hs := productUnit_symbol (n + 1)
    (Units.map (algebraMap S E).toMonoidHom ∘ u) (Additive.ofMul (endpointParameter k E a))
  simp only [toMul_ofMul] at hs
  rw [← hs]
  change linearResidue a (n + 1)
    (finiteExtensionNorm (RatFunc k) E (n + 1 + 1)
      (productUnit (n + 1) (symbol (Units.map (algebraMap S E).toMonoidHom ∘ u))
        (MilnorK.K2.unitsLinear (algebraMap (RatFunc k) E)
          (Additive.ofMul (polynomialUnit (X - C a) (irreducible_X_sub_C a).ne_zero))))) = _
  rw [finiteExtensionNorm_productUnit_constants_right]
  exact linearResidue_norm_ring_unit_symbol_productUnit k S E a n u

/-- Any two actual endpoint branch sums agree, with every branch and its full
order retained. No endpoint-boundary compatibility is assumed. -/
theorem endpointWeightedResidueSum_eq (a b : k) (n : ℕ) (u : Fin (n + 1) → Sˣ) :
    endpointWeightedResidueSum k S E a (n + 1) u =
      endpointWeightedResidueSum k S E b (n + 1) u := by
  rw [endpointWeightedResidueSum_eq_specialization,
    endpointWeightedResidueSum_eq_specialization]
  exact linearSpecialization_norm_ring_unit_symbol_eq k S E a b n u

end MilnorK.DedekindResidue
