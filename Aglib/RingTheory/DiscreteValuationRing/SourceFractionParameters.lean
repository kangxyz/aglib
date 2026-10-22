/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.ParameterPoint
public import Aglib.RingTheory.AlgebraicIndependent.Localization
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Residual parameters in the actual source fraction field

The coefficient action on the source fraction field is the native
`FractionRing.liftAlgebra`, constructed from injectivity of the original
coefficient map. No independently chosen fraction-field action is assumed.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace ParameterLocalization

universe u v w t

variable {R : Type u} {S : Type v} {B : Type w} {ι : Type t}
variable [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
variable [CommRing B] [IsDomain B] [Algebra R B] [Algebra R S]
variable [IsLocalHom (algebraMap R S)] (p : R) [Fact (Irreducible p)]

omit [IsLocalHom (algebraMap R S)] [IsDomain B] in
/-- The coefficient action on the source is faithful because its composite
through the actual point preserves a uniformizer. The point need not be injective. -/
theorem faithfulSMul_source_of_map_irreducible (χ : B →ₐ[R] S)
    (hpS : Irreducible (algebraMap R S p)) : FaithfulSMul R B := by
  apply (faithfulSMul_iff_algebraMap_injective R B).mpr
  intro r s h
  apply IsDiscreteValuationRing.injective_of_map_irreducible (algebraMap R S)
    (Fact.out : Irreducible p) hpS
  rw [← χ.commutes r, ← χ.commutes s, h]

/-- Residually independent source parameters are independent over the original
fraction field inside the source fraction field, giving its actual transcendence-degree bound. -/
theorem fractionRing_independent_and_trdeg_bound [Finite ι]
    (χ : B →ₐ[R] S) (hpS : Irreducible (algebraMap R S p)) (b : ι → B)
    (hb : AlgebraicIndependent (ResidueField R) (fun i => residue S (χ (b i)))) :
    letI : FaithfulSMul R B := faithfulSMul_source_of_map_irreducible p χ hpS
    letI : Algebra (FractionRing R) (FractionRing B) :=
      FractionRing.liftAlgebra R (FractionRing B)
    AlgebraicIndependent (FractionRing R) (fun i => algebraMap B (FractionRing B) (b i)) ∧
      Cardinal.lift.{w} (Cardinal.mk ι) ≤
        Cardinal.lift.{t} (Algebra.trdeg (FractionRing R) (FractionRing B)) := by
  let : FaithfulSMul R B := faithfulSMul_source_of_map_irreducible p χ hpS
  let : Algebra (FractionRing R) (FractionRing B) :=
    FractionRing.liftAlgebra R (FractionRing B)
  let : IsScalarTower R (FractionRing R) (FractionRing B) :=
    FractionRing.isScalarTower_liftAlgebra R (FractionRing B)
  have ht : AlgebraicIndependent R (χ ∘ b) :=
    algebraicIndependent_of_residue p (χ ∘ b) hb hpS
  have hs : AlgebraicIndependent R b := AlgebraicIndependent.of_comp χ ht
  have hk : AlgebraicIndependent R (algebraMap B (FractionRing B) ∘ b) :=
    hs.map' (f := IsScalarTower.toAlgHom R B (FractionRing B))
      (IsFractionRing.injective B (FractionRing B))
  have hf : AlgebraicIndependent (FractionRing R)
      (algebraMap B (FractionRing B) ∘ b) := hk.localization (nonZeroDivisors R)
  exact ⟨hf, hf.lift_cardinalMk_le_trdeg⟩

end ParameterLocalization
