/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Residue.Change
public import Aglib.KTheory.MilnorK.Residue.Compatibility
public import Aglib.KTheory.MilnorK.K3.DVR

/-!
# Canonical tame residues of actual discrete valuation rings in every degree

The background maps are the existing valuation and actual residue-unit map
of a DVR and its fraction field. The proved unit-part-change formula makes
the all-degree tame residue independent of the chosen irreducible uniformizer.
The normalization places that uniformizer last; the actual ring-unit and
principal-unit formulas allow arbitrary other fraction-field units.

The degree-three adapter agrees with the original `MilnorK3.DVR.residue` on
every class. No residue law, norm or reciprocity statement is supplied as data.
-/

@[expose] public noncomputable section

namespace MilnorK.DVR

variable (R L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]

/-- All-degree tame residue from the actual data of a specified DVR uniformizer. -/
def residueWithUniformizer {π : R} (hπ : Irreducible π) (n : ℕ) :
    K L (n + 1) →ₗ[ℤ] K (IsLocalRing.ResidueField R) n :=
  MilnorK.residue (MilnorK.K2.DVR.data (K := L) hπ)
    (MilnorK.K2.DVR.unitReductionCompatible hπ) n

/-- Every two actual uniformizers give the same tame map in every degree. -/
theorem residueWithUniformizer_independent {π π' : R}
    (hπ : Irreducible π) (hπ' : Irreducible π') (n : ℕ) :
    residueWithUniformizer R L hπ' n = residueWithUniformizer R L hπ n := by
  unfold residueWithUniformizer
  exact residue_eq_of_unitPart_change (MilnorK.K2.DVR.data (K := L) hπ)
    (MilnorK.K2.DVR.data (K := L) hπ')
    (MilnorK.K2.DVR.unitReductionCompatible hπ) (MilnorK.K2.DVR.unitReductionCompatible hπ')
    (MilnorK.K2.DVR.uniformizerChange hπ hπ') (fun _ => rfl)
    (MilnorK.K2.DVR.unitPart_change (K := L) hπ hπ') n

/-- The canonical all-degree residue of an actual DVR and its fraction field. -/
def residue (n : ℕ) : K L (n + 1) →ₗ[ℤ] K (IsLocalRing.ResidueField R) n :=
  residueWithUniformizer R L (IsDiscreteValuationRing.exists_irreducible R).choose_spec n

/-- The canonical residue agrees with the construction using every actual uniformizer. -/
theorem residue_eq {π : R} (hπ : Irreducible π) (n : ℕ) :
    residue R L n = residueWithUniformizer R L hπ n :=
  residueWithUniformizer_independent R L hπ
    (IsDiscreteValuationRing.exists_irreducible R).choose_spec n

/-- Degree one is the original normalized integer valuation of the fraction field. -/
theorem zeroEquiv_residue (x : K L 1) :
    zeroEquiv (IsLocalRing.ResidueField R) (residue R L 0 x) =
      MilnorK.K2.DVR.value R L (oneEquiv L x) :=
  MilnorK.zeroEquiv_residue (MilnorK.K2.DVR.chosenData R L)
    (MilnorK.K2.DVR.chosenData_unitReductionCompatible R L) x

/-- Every symbol of actual embedded ring units has zero residue. -/
theorem residue_ring_units (n : ℕ) (a : Fin (n + 1) → Rˣ) :
    residue R L n (symbol (MilnorK.K2.DVR.fieldUnits R L ∘ a)) = 0 :=
  residue_symbol_units (MilnorK.K2.DVR.chosenData R L)
    (MilnorK.K2.DVR.chosenData_unitReductionCompatible R L) n _
    (fun i => MilnorK.K2.DVR.value_fieldUnits R L (a i))

/-- Last-slot uniformizer normalization uses the literal ring residue map, also in degree one. -/
theorem residue_ring_units_uniformizer {π : R} (hπ : Irreducible π)
    (n : ℕ) (a : Fin n → Rˣ) :
    residue R L n (symbol (Fin.snoc (MilnorK.K2.DVR.fieldUnits R L ∘ a)
      (MilnorK.K2.DVR.uniformizer (K := L) hπ))) =
      symbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a) := by
  rw [residue_eq R L hπ n]
  have h := residue_symbol_uniformizer (MilnorK.K2.DVR.data (K := L) hπ)
    (MilnorK.K2.DVR.unitReductionCompatible hπ) n (MilnorK.K2.DVR.fieldUnits R L ∘ a)
    (fun i => MilnorK.K2.DVR.value_fieldUnits R L (a i))
  refine h.trans ?_
  apply congrArg symbol
  funext i
  exact MilnorK.K2.DVR.unitResidue_fieldUnits hπ (a i)

/-- A principal ring-unit coordinate kills the residue without restricting other coordinates. -/
theorem residue_principal_ring_unit (n : ℕ) (a : SymbolTuple L (n + 1))
    (i : Fin (n + 1)) (u : Rˣ) (hi : a i = MilnorK.K2.DVR.fieldUnits R L u)
    (hu : Units.map (IsLocalRing.residue R).toMonoidHom u = 1) :
    residue R L n (symbol a) = 0 := by
  apply residue_symbol_principal (MilnorK.K2.DVR.chosenData R L)
    (MilnorK.K2.DVR.chosenData_unitReductionCompatible R L) n a i
  · rw [hi]
    exact MilnorK.K2.DVR.value_fieldUnits R L u
  · rw [hi]
    change Additive.ofMul (MilnorK.K2.DVR.unitResidue
      (IsDiscreteValuationRing.exists_irreducible R).choose_spec
      (MilnorK.K2.DVR.fieldUnits R L u)) = 0
    rw [MilnorK.K2.DVR.unitResidue_fieldUnits, hu]
    rfl

/-- All repeated-uniformizer sign contributions survive in the actual DVR residue. -/
theorem residue_uniformizers {π : R} (hπ : Irreducible π) (n : ℕ) :
    residue R L n (symbol (fun _ => MilnorK.K2.DVR.uniformizer (K := L) hπ)) =
      symbol (fun _ => (-1 : (IsLocalRing.ResidueField R)ˣ)) := by
  rw [residue_eq R L hπ n]
  exact residue_symbol_uniformizers (MilnorK.K2.DVR.data (K := L) hπ)
    (MilnorK.K2.DVR.unitReductionCompatible hπ) n

/-- Degree two agrees with the old tame map from the original chosen actual DVR data. -/
theorem oneEquiv_residue_one (x : K L 2) :
    oneEquiv (IsLocalRing.ResidueField R) (residue R L 1 x) =
      MilnorK.K2.tame (MilnorK.K2.DVR.chosenData R L) (twoEquiv L x) :=
  MilnorK.oneEquiv_residue_one (MilnorK.K2.DVR.chosenData R L)
    (MilnorK.K2.DVR.chosenData_unitReductionCompatible R L) x

/-- The degree-three actual DVR map is the original one on all quotient classes. -/
theorem twoEquiv_residue_two (x : K L 3) :
    twoEquiv (IsLocalRing.ResidueField R) (residue R L 2 x) =
      MilnorK.K3.DVR.residue R L (threeEquiv L x) :=
  MilnorK.twoEquiv_residue_two (MilnorK.K2.DVR.chosenData R L)
    (MilnorK.K2.DVR.chosenData_unitReductionCompatible R L) x

end MilnorK.DVR
