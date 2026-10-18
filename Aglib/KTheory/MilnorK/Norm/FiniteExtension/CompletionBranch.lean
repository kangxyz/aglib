/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.Complete
public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.CompletionResidues

/-!
# One original branch computed by its actual completed fraction norm

The completed ring diagram supplies finite algebras and scalar towers, not a
norm-residue law. The proved general complete-DVR theorem and the original
completion residue identifications yield the branch formula.
-/

@[expose] public noncomputable section

namespace MilnorK

open IsLocalRing

universe u

variable (R S E : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CharZero (ResidueField R)]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
  [FiniteDimensional (ResidueField R) (ResidueField S)]
  [Field E] [Algebra S E] [IsFractionRing S E]


variable [Algebra (AdicCompletion (maximalIdeal R) R) (AdicCompletion (maximalIdeal S) S)]
    [IsLocalHom (algebraMap (AdicCompletion (maximalIdeal R) R) (AdicCompletion (maximalIdeal
    S) S))] [Module.Finite (AdicCompletion (maximalIdeal R) R) (AdicCompletion (maximalIdeal S)
    S)]
  [IsScalarTower R (AdicCompletion (maximalIdeal R) R) (AdicCompletion (maximalIdeal S) S)]
    [Algebra (FractionRing (AdicCompletion (maximalIdeal R) R)) (FractionRing (AdicCompletion
    (maximalIdeal S) S))]
  [IsScalarTower (AdicCompletion (maximalIdeal R) R) (FractionRing (AdicCompletion
    (maximalIdeal R) R)) (FractionRing (AdicCompletion (maximalIdeal S) S))]
  [FiniteDimensional (FractionRing (AdicCompletion
    (maximalIdeal R) R)) (FractionRing (AdicCompletion (maximalIdeal S) S))]

/-- Every class on the original branch satisfies the completed norm formula;
all residue fields and all completion maps are literal. -/
theorem residue_completed_norm_eq_original_branch (n : ℕ) (x : K E (n + 1)) :
    let _ : CharZero (FractionRing (AdicCompletion (maximalIdeal R) R)) := by
      let _ : CharZero (AdicCompletion (maximalIdeal R) R) := RingHom.charZero
        ((AdicCompletion.residueFieldEquiv R).toRingHom.comp (IsLocalRing.residue
    (AdicCompletion (maximalIdeal R) R)))
      exact charZero_of_injective_algebraMap (IsFractionRing.injective (AdicCompletion
    (maximalIdeal R) R) (FractionRing (AdicCompletion (maximalIdeal R) R)))
    map n (AdicCompletion.residueFieldEquiv R).toRingHom
      (DVR.residue (AdicCompletion (maximalIdeal R) R) (FractionRing (AdicCompletion
    (maximalIdeal R) R)) n (finiteExtensionNorm (FractionRing (AdicCompletion (maximalIdeal R)
    R)) (FractionRing (AdicCompletion (maximalIdeal S) S)) (n + 1)
        (map (n + 1) (AdicCompletion.fractionRingMap S E) x))) =
      finiteExtensionNorm (ResidueField R) (ResidueField S) n (DVR.residue S E n x) := by
  dsimp only
  let : CharZero (ResidueField (AdicCompletion (maximalIdeal R) R)) :=
    charZero_of_injective_ringHom (AdicCompletion.residueFieldEquiv R).symm.injective
  let : CharZero (AdicCompletion (maximalIdeal R) R) := RingHom.charZero (IsLocalRing.residue
    (AdicCompletion (maximalIdeal R) R))
  let : CharZero (FractionRing (AdicCompletion (maximalIdeal R) R)) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (AdicCompletion (maximalIdeal R)
    R) (FractionRing (AdicCompletion (maximalIdeal R) R)))
  rw [residue_finiteExtensionNorm_complete (AdicCompletion (maximalIdeal R) R) (FractionRing
    (AdicCompletion (maximalIdeal R) R)) (FractionRing (AdicCompletion (maximalIdeal S) S))
    (AdicCompletion (maximalIdeal S) S)]
  rw [finiteExtensionNorm_completionResidueEquiv R S]
  rw [DVR.residue_completion_identification]

end MilnorK
