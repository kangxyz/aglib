/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Residue.AdicCompletion
public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.Equiv

/-!
# Actual residue norm identifications in a completion square

The ring scalar tower forces the residue-field square. Norm naturality then
identifies the completed residue norm with the original residue norm; neither
residue compatibility nor a norm-square hypothesis is an input.
-/

@[expose] public noncomputable section

namespace MilnorK

open IsLocalRing

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
  [Algebra (AdicCompletion (maximalIdeal R) R) (AdicCompletion (maximalIdeal S) S)]
  [IsLocalHom (algebraMap (AdicCompletion (maximalIdeal R) R)
    (AdicCompletion (maximalIdeal S) S))]
  [IsScalarTower R (AdicCompletion (maximalIdeal R) R) (AdicCompletion (maximalIdeal S) S)]

/-- The completion residue equivalences commute with the original residue map. -/
theorem completionResidueEquiv_algebraMap
    (a : ResidueField (AdicCompletion (maximalIdeal R) R)) :
    AdicCompletion.residueFieldEquiv S
      (algebraMap (ResidueField (AdicCompletion (maximalIdeal R) R))
        (ResidueField (AdicCompletion (maximalIdeal S) S)) a) =
      algebraMap (ResidueField R) (ResidueField S) (AdicCompletion.residueFieldEquiv R a) := by
  obtain ⟨b, rfl⟩ := (AdicCompletion.residueField_map_bijective R).2 a
  rw [AdicCompletion.residueFieldEquiv_map]
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective b
  change AdicCompletion.residueFieldEquiv S
      (IsLocalRing.residue (AdicCompletion (maximalIdeal S) S)
        (algebraMap (AdicCompletion (maximalIdeal R) R) (AdicCompletion (maximalIdeal S) S)
          (algebraMap R (AdicCompletion (maximalIdeal R) R) r))) =
    IsLocalRing.residue S (algebraMap R S r)
  rw [← IsScalarTower.algebraMap_apply R (AdicCompletion (maximalIdeal R) R),
    IsScalarTower.algebraMap_apply R S (AdicCompletion (maximalIdeal S) S)]
  exact AdicCompletion.residueFieldEquiv_map S (IsLocalRing.residue S (algebraMap R S r))

/-- Both residue norms use the actual fields and actual scalar maps. -/
theorem finiteExtensionNorm_completionResidueEquiv
    [CharZero (ResidueField R)]
    [FiniteDimensional (ResidueField R) (ResidueField S)]
    [FiniteDimensional (ResidueField (AdicCompletion (maximalIdeal R) R))
      (ResidueField (AdicCompletion (maximalIdeal S) S))]
    (n : ℕ) (x : K (ResidueField (AdicCompletion (maximalIdeal S) S)) n) :
    let _ : CharZero (ResidueField (AdicCompletion (maximalIdeal R) R)) :=
      charZero_of_injective_ringHom (AdicCompletion.residueFieldEquiv R).symm.injective
    map n (AdicCompletion.residueFieldEquiv R).toRingHom
      (finiteExtensionNorm (ResidueField (AdicCompletion (maximalIdeal R) R))
        (ResidueField (AdicCompletion (maximalIdeal S) S)) n x) =
      finiteExtensionNorm (ResidueField R) (ResidueField S) n
        (map n (AdicCompletion.residueFieldEquiv S).toRingHom x) := by
  dsimp only
  let : CharZero (ResidueField (AdicCompletion (maximalIdeal R) R)) :=
    charZero_of_injective_ringHom (AdicCompletion.residueFieldEquiv R).symm.injective
  exact finiteExtensionNorm_equiv (AdicCompletion.residueFieldEquiv R)
    (AdicCompletion.residueFieldEquiv S) (completionResidueEquiv_algebraMap R S) n x

end MilnorK
