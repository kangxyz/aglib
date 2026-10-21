/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.SeparableResidueExtension
public import Aglib.RingTheory.DiscreteValuationRing.SelectedEtaleBaseChange

/-! # The actual same-uniformizer separable residue square

The source DVR and selected tensor target DVR are constructed, not postulated.
The prescribed residue embedding determines the selected target point. The
same-uniformizer premise on the original DVR pair is retained explicitly.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace SeparableResidueExtension

variable (R E S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field E] [Algebra (ResidueField R) E] [Module.Finite (ResidueField R) E]
  [Algebra.IsSeparable (ResidueField R) E]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)]
  (e : E →ₐ[ResidueField R] ResidueField S)

/-- The base DVR acts on the specified residue extension through its residue map. -/
local instance residueSquareBaseAlgebra : Algebra R E :=
  ((algebraMap (ResidueField R) E).comp (residue R)).toAlgebra

local instance : IsScalarTower R (ResidueField R) E :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The actual selected point over the given residue embedding. -/
def targetPoint : Ring R E →ₐ[R] ResidueField S :=
  (e.restrictScalars R).comp (localPoint R E)

instance targetPoint_isLocalHom : IsLocalHom (targetPoint R E S e).toRingHom := by
  let : IsLocalHom e.toRingHom := inferInstance
  exact RingHom.isLocalHom_comp e.toRingHom (localPoint R E).toRingHom

/-- The actual localization of the actual base-changed source DVR. -/
abbrev TargetRing :=
  Algebra.SelectedEtaleBaseChange.Ring R (Ring R E) S (targetPoint R E S e)

instance targetRing_isDomain : IsDomain (TargetRing R E S e) := inferInstance

instance targetRing_isDiscreteValuationRing :
    IsDiscreteValuationRing (TargetRing R E S e) := inferInstance

instance targetRing_algebraMap_isLocalHom :
    IsLocalHom (algebraMap S (TargetRing R E S e)) := inferInstance

/-- The actual top-right map in the selected residue square. -/
def targetMap : Ring R E →ₐ[R] TargetRing R E S e :=
  Algebra.SelectedEtaleBaseChange.rightMap R (Ring R E) S (targetPoint R E S e)

instance targetMap_isLocalHom : IsLocalHom (targetMap R E S e).toRingHom :=
  Algebra.SelectedEtaleBaseChange.rightMap_isLocalHom R (Ring R E) S (targetPoint R E S e)

/-- The original coefficient square commutes literally. -/
theorem targetMap_algebraMap (r : R) :
    targetMap R E S e (algebraMap R (Ring R E) r) =
      algebraMap S (TargetRing R E S e) (algebraMap R S r) := by
  rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply R S (TargetRing R E S e)]

/-- The actual selected target retains the original target residue field. -/
def targetResidueEquiv : ResidueField (TargetRing R E S e) ≃+* ResidueField S :=
  Algebra.SelectedEtaleBaseChange.residueEquiv R (Ring R E) S (targetPoint R E S e)

/-- Its comparison is the inverse of the native S-residue map. -/
@[simp] theorem targetResidueEquiv_map (x : ResidueField S) :
    targetResidueEquiv R E S e
      (ResidueField.map (algebraMap S (TargetRing R E S e)) x) = x :=
  Algebra.SelectedEtaleBaseChange.residueEquiv_map R (Ring R E) S (targetPoint R E S e) x

/-- The native right residue map is the prescribed embedding
after the actual residue comparisons. -/
theorem targetResidueEquiv_rightMap (x : ResidueField (Ring R E)) :
    targetResidueEquiv R E S e (ResidueField.map (targetMap R E S e).toRingHom x) =
      e (residueEquiv R E x) := by
  obtain ⟨a, rfl⟩ := residue_surjective x
  rw [ResidueField.map_residue]
  change Algebra.SelectedEtaleBaseChange.residueEquiv R (Ring R E) S (targetPoint R E S e)
    (residue (TargetRing R E S e)
      (Algebra.SelectedEtaleBaseChange.rightMap R (Ring R E) S (targetPoint R E S e) a)) = _
  rw [Algebra.SelectedEtaleBaseChange.residueEquiv_residue,
    Algebra.SelectedEtaleBaseChange.point_rightMap, residueEquiv_residue]
  rfl

/-- A uniformizer of S remains a uniformizer in the selected target DVR. -/
theorem target_irreducible_algebraMap {π : S} (hπ : Irreducible π) :
    Irreducible (algebraMap S (TargetRing R E S e) π) :=
  Algebra.SelectedEtaleBaseChange.irreducible_algebraMap R (Ring R E) S
    (targetPoint R E S e) hπ

/-- The original same-uniformizer condition is preserved by the constructed square.
A mere local R→S map does not imply this condition and is not substituted for it. -/
theorem targetMap_preserves_uniformizer {π : R}
    (hπS : Irreducible (algebraMap R S π)) :
    Irreducible (targetMap R E S e (algebraMap R (Ring R E) π)) := by
  rw [targetMap_algebraMap]
  exact target_irreducible_algebraMap R E S e hπS

end SeparableResidueExtension
