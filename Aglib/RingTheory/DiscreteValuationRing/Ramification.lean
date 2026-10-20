/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.DiscreteValuationRing.AngularComponent
public import Aglib.Algebra.Group.TwoTorsionSign
public import Aglib.Algebra.Group.Units.Map

/-!
# Canonical order and angular-residue transport for local DVR maps

The actual ring and fraction-field maps form the stated commuting square.
The index is derived from the target order of a chosen source uniformizer,
is independent of that choice, and is positive for a local map. Normalized
unit residues retain their exact uniformizer correction. Additive notation
uses direct Mathlib units and their integer-linear maps; no K-group or tame
map is imported.
-/

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/DiscreteValuationRing/Ramification.lean` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`18a15e41fca473bfb493ff3f8df1b2f49b8363f80ced76e154fee7e702acfc0f`.
-/

@[expose] public section

noncomputable section

namespace IsDiscreteValuationRing.Ramification

open IsLocalRing IsDiscreteValuationRing

variable {R S K L : Type*}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L]

/-- Every nonzero fraction is its normalized DVR unit times a uniformizer power. -/
theorem unit_uniformizer_decomposition {π : R} (hπ : Irreducible π) (a : Additive Kˣ) :
    a = Additive.ofMul (fractionUnits R K (angularComponent (K := K) hπ a.toMul)) +
      fractionOrderLinear R K a • Additive.ofMul (uniformizerUnit (K := K) hπ) := by
  apply Additive.toMul.injective
  change a.toMul = fractionUnits R K (angularComponent hπ a.toMul) *
    uniformizerUnit (K := K) hπ ^ fractionOrder R K a.toMul
  rw [fractionUnits_angularComponent]
  simp [normalizedUnit, mul_assoc]

section CompatibleFields

variable (f : R →+* S) (F : K →+* L)
variable (compat : ∀ r : R, F (algebraMap R K r) = algebraMap S L (f r))

include compat

omit [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    [IsFractionRing R K] [IsFractionRing S L] in
/-- A compatible field map takes actual integral units to their ring-map images. -/
theorem map_fractionUnits (u : Rˣ) :
    Units.map F.toMonoidHom (fractionUnits R K u) =
      fractionUnits S L (Units.map f.toMonoidHom u) :=
  by
    apply Units.ext
    exact compat (u : R)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    [IsFractionRing R K] [IsFractionRing S L] in
/-- The additive presentation of the same compatibility on integral units. -/
theorem unitsLinear_fractionUnits (u : Rˣ) :
    Units.mapAdditiveLinear F.toMonoidHom (Additive.ofMul (fractionUnits R K u)) =
      Additive.ofMul (fractionUnits S L (Units.map f.toMonoidHom u)) :=
  congrArg Additive.ofMul (map_fractionUnits f F compat u)

/-- Valuations scale by the actual order of the image of any source uniformizer. -/
theorem value_map_uniformizer {π : R} (hπ : Irreducible π) (a : Additive Kˣ) :
    fractionOrderLinear S L (Units.mapAdditiveLinear F.toMonoidHom a) =
      fractionOrderLinear S L (Units.mapAdditiveLinear F.toMonoidHom
      (Additive.ofMul (uniformizerUnit (K := K) hπ))) *
        fractionOrderLinear R K a := by
  have h := congrArg (fun b => fractionOrderLinear S L (Units.mapAdditiveLinear F.toMonoidHom b))
    (unit_uniformizer_decomposition hπ a)
  simpa only [map_add, map_smul, unitsLinear_fractionUnits f F compat,
    fractionOrderLinear_fractionUnits, zero_add, smul_eq_mul, mul_comm] using h

omit compat in
/-- The ramification index defined using the source DVR's actual chosen uniformizer. -/
def ramificationIndex (R S : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    (F : K →+* L) : ℤ :=
  fractionOrderLinear S L (Units.mapAdditiveLinear F.toMonoidHom
    (Additive.ofMul (uniformizerUnit (K := K)
      (IsDiscreteValuationRing.exists_irreducible R).choose_spec)))

/-- The canonical integer valuations scale by the constructed index. -/
theorem value_map (a : Additive Kˣ) :
    fractionOrderLinear S L (Units.mapAdditiveLinear F.toMonoidHom a) =
      ramificationIndex R S F * fractionOrderLinear R K a :=
  value_map_uniformizer f F compat
    (IsDiscreteValuationRing.exists_irreducible R).choose_spec a

/-- The index is independent of which actual irreducible uniformizer is used. -/
theorem ramificationIndex_eq {π : R} (hπ : Irreducible π) :
    ramificationIndex R S F =
      fractionOrderLinear S L (Units.mapAdditiveLinear F.toMonoidHom
        (Additive.ofMul (uniformizerUnit (K := K) hπ))) := by
  simpa using (value_map f F compat (Additive.ofMul (uniformizerUnit (K := K) hπ))).symm

variable [IsLocalHom f]

/-- Localness forces positive order for the nonzero image of a uniformizer. -/
theorem value_map_uniformizer_pos {π : R} (hπ : Irreducible π) :
    0 < fractionOrderLinear S L (Units.mapAdditiveLinear F.toMonoidHom
      (Additive.ofMul (uniformizerUnit (K := K) hπ))) := by
  change 0 < fractionOrder S L (Units.map F.toMonoidHom (uniformizerUnit hπ))
  apply (fractionValuation_lt_one_iff _).mp
  change fractionValuation S L (F (algebraMap R K π)) < 1
  rw [compat]
  exact ((IsDiscreteValuationRing.maximalIdeal S).valuation_lt_one_iff_mem
    (K := L) (f π)).mpr (map_nonunit f π hπ.not_isUnit)

/-- The constructed ramification index is strictly positive. -/
theorem ramificationIndex_pos : 0 < ramificationIndex R S F :=
  value_map_uniformizer_pos f F compat
    (IsDiscreteValuationRing.exists_irreducible R).choose_spec

end CompatibleFields

section ResidueMaps

variable (f : R →+* S) [IsLocalHom f]

/-- The actual residue-field map on multiplicative units. -/
def residueUnitsMap : (ResidueField R)ˣ →* (ResidueField S)ˣ :=
  Units.map (ResidueField.map f).toMonoidHom

/-- The actual residue-field map on units, in integer-linear additive notation. -/
def residueLinear : Additive (ResidueField R)ˣ →ₗ[ℤ] Additive (ResidueField S)ˣ :=
  Units.mapAdditiveLinear (ResidueField.map f).toMonoidHom

/-- The quotient map commutes with reduction of every integral unit. -/
theorem residueUnitsMap_residue (u : Rˣ) :
    residueUnitsMap f (Units.map (residue R).toMonoidHom u) =
      Units.map (residue S).toMonoidHom (Units.map f.toMonoidHom u) := by
  apply Units.ext
  exact ResidueField.map_residue f (u : R)

/-- Reduction of the sign commutes with the actual residue-field map. -/
@[simp] theorem residueLinear_sign : residueLinear f (Additive.ofMul (-1 : (ResidueField R)ˣ)) =
    Additive.ofMul (-1 : (ResidueField S)ˣ) := by
  apply Additive.toMul.injective
  apply Units.ext
  change ResidueField.map f (-1) = -1
  simp

end ResidueMaps

/-- For a local algebra map, the induced residue map is the actual residue algebra map. -/
theorem residueMap_algebraMap [Algebra R S] [IsLocalHom (algebraMap R S)] :
    ResidueField.map (algebraMap R S) = algebraMap (ResidueField R) (ResidueField S) := by
  apply RingHom.ext
  intro x
  obtain ⟨r, rfl⟩ := residue_surjective x
  rfl

/-- The multiplicative unit map agrees with the actual residue algebra map. -/
theorem residueUnitsMap_algebraMap [Algebra R S] [IsLocalHom (algebraMap R S)] :
    residueUnitsMap (algebraMap R S) =
      Units.map (algebraMap (ResidueField R) (ResidueField S)).toMonoidHom := by
  rw [residueUnitsMap, residueMap_algebraMap]

/-- The linear residue-unit map agrees with the map from the actual residue algebra. -/
theorem residueLinear_algebraMap [Algebra R S] [IsLocalHom (algebraMap R S)] :
    residueLinear (algebraMap R S) =
      Units.mapAdditiveLinear
        (algebraMap (ResidueField R) (ResidueField S)).toMonoidHom := by
  rw [residueLinear, residueMap_algebraMap]

/-- Angular reduction of an actual DVR unit is its ordinary residue. -/
theorem unitPart_fractionUnits {π : R} (hπ : Irreducible π) (u : Rˣ) :
    angularResidueLinear (K := K) hπ (Additive.ofMul (fractionUnits R K u)) =
      Additive.ofMul (Units.map (residue R).toMonoidHom u) :=
  by
    change Additive.ofMul (angularResidue hπ (fractionUnits R K u)) = _
    rw [angularResidue_fractionUnits]
    rfl

/-- Unfold angular reduction to the actual residue of its normalized unit lift. -/
theorem unitPart_apply {π : R} (hπ : Irreducible π) (a : Additive Kˣ) :
    angularResidueLinear (K := K) hπ a =
      Additive.ofMul (Units.map (residue R).toMonoidHom (angularComponent hπ a.toMul)) := rfl

section TameNaturality

variable (f : R →+* S) [IsLocalHom f] (F : K →+* L)
variable (compat : ∀ r : R, F (algebraMap R K r) = algebraMap S L (f r))

include compat

omit [IsFractionRing R K] in
/-- On integral units, angular reduction commutes with the actual local map. -/
theorem unitPart_map_fractionUnits {ρ : S} (hρ : Irreducible ρ) (u : Rˣ) :
    angularResidueLinear (K := L) hρ
        (Units.mapAdditiveLinear F.toMonoidHom (Additive.ofMul (fractionUnits R K u))) =
      residueLinear f (Additive.ofMul (Units.map (residue R).toMonoidHom u)) := by
  rw [unitsLinear_fractionUnits f F compat, unitPart_fractionUnits]
  exact (congrArg Additive.ofMul (residueUnitsMap_residue f u)).symm

/-- The exact angular-component correction is the source order times the
target angular component of the image of the source uniformizer. -/
theorem unitPart_map {π : R} {ρ : S} (hπ : Irreducible π) (hρ : Irreducible ρ)
    (a : Additive Kˣ) :
    angularResidueLinear (K := L) hρ (Units.mapAdditiveLinear F.toMonoidHom a) =
      residueLinear f (angularResidueLinear (K := K) hπ a) +
        fractionOrderLinear R K a • angularResidueLinear (K := L) hρ
          (Units.mapAdditiveLinear F.toMonoidHom
            (Additive.ofMul (uniformizerUnit (K := K) hπ))) := by
  have h := congrArg
    (fun b => angularResidueLinear (K := L) hρ (Units.mapAdditiveLinear F.toMonoidHom b))
    (unit_uniformizer_decomposition hπ a)
  simpa only [map_add, map_smul, unitPart_map_fractionUnits f F compat hρ,
    unitPart_apply] using h

end TameNaturality
end IsDiscreteValuationRing.Ramification
