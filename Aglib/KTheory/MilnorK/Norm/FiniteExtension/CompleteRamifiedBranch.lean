/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.CompletePGroup
public import Aglib.KTheory.MilnorK.Residue.RamifiedRestriction

/-!
# The ramification-weighted upper branch square

The proved complete p-group square is applied after the actual upper field
restriction. Ramified residue naturality supplies exactly the upper vertical
ramification exponent, with no compatibility premise or exponent cancellation.
-/

@[expose] public noncomputable section

namespace MilnorK

open IsLocalRing

universe u

/-- Each actual upper p-group branch contributes its literal ramification weight. -/
theorem residue_norm_restrict_complete_pGroup_branch
    (S T U E L D Ω : Type u)
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [IsAdicComplete (maximalIdeal T) T] [CharZero (ResidueField T)]
    [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    [Field E] [Algebra S E] [IsFractionRing S E]
    [Field L] [CharZero L] [Algebra T L] [IsFractionRing T L]
    [Field D] [CharZero D] [Algebra L D] [FiniteDimensional L D]
    [Algebra T D] [IsScalarTower T L D]
    [Algebra T U] [Module.Finite T U] [IsLocalHom (algebraMap T U)]
    [Algebra U D] [IsScalarTower T U D] [IsFractionRing U D]
    [IsIntegralClosure U T D]
    [Field Ω] [Algebra L Ω] [FiniteDimensional L Ω] [IsGalois L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[L] Ω)) (g : D →ₐ[L] Ω)
    (j : S →+* U) [IsLocalHom j] (f : E →+* D)
    (hf : ∀ s, f (algebraMap S E s) = algebraMap U D (j s))
    {ϖ : S} {ρ : U} (hϖ : Irreducible ϖ) (hρ : Irreducible ρ)
    (w : Uˣ) (b : ℕ) (hb : j ϖ = (w : U) * ρ ^ b)
    (n : ℕ) (x : K E (n + 1)) :
    DVR.residue T L n (finiteExtensionNorm L D (n + 1) (map (n + 1) f x)) =
      b • finiteExtensionNorm (ResidueField T) (ResidueField U) n
        (map n (ResidueField.map j) (DVR.residue S E n x)) := by
  rw [residue_finiteExtensionNorm_complete_of_pGroup T U L D Ω ℓ hG g,
    DVR.residue_ramified_restrict_apply j f hf hϖ hρ w b hb,
    map_smul, natCast_zsmul]

end MilnorK
