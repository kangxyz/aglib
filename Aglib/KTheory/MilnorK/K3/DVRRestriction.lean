/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.DVR
public import Aglib.KTheory.MilnorK.K3.Map

/-!
# Unramified restriction of the actual DVR Milnor K₃ residue

A local homomorphism of actual DVRs, together with a commuting map of their
fraction fields, induces a map of their actual residue fields. If a source
uniformizer remains irreducible in the target, the degree-three residue
commutes with field restriction. Integer orders and normalized unit residues
are derived from `normalizedLift_spec`; neither compatibility is an input.
The theorem concerns the original Milnor tensor quotients and ramification
index one only.
-/

@[expose] public noncomputable section

namespace MilnorK.K3.DVR

open MilnorK.K2

private theorem map_symbolBilinear {k l : Type*} [Field k] [Field l]
    (f : k →+* l) (a b : UnitsAdd k) :
    MilnorK.K2.map f (symbolBilinear k a b) =
      symbolBilinear l (unitsLinear f a) (unitsLinear f b) := rfl

private theorem unitsLinear_residueSign {k l : Type*} [Field k] [Field l]
    (f : k →+* l) : unitsLinear f (residueSign k) = residueSign l := by
  change Additive.ofMul (Units.map f.toMonoidHom (-1)) = Additive.ofMul (-1)
  congr 1
  apply Units.ext
  change f (-1) = -1
  simp

variable {R S K L : Type*}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L]

/-- The literal residue-field map induced by the local ring homomorphism. -/
abbrev residueFieldMap (j : R →+* S) [IsLocalHom j] :
    IsLocalRing.ResidueField R →+* IsLocalRing.ResidueField S :=
  IsLocalRing.ResidueField.map j

/-- This map commutes with the two original ring residue homomorphisms. -/
theorem residueFieldMap_residue (j : R →+* S) [IsLocalHom j] (r : R) :
    residueFieldMap j (IsLocalRing.residue R r) = IsLocalRing.residue S (j r) :=
  IsLocalRing.ResidueField.map_residue j r

variable (j : R →+* S) (F : K →+* L)
  (hF : ∀ r : R, F (algebraMap R K r) = algebraMap S L (j r))

include hF

omit [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S]
  [IsDiscreteValuationRing S] [IsFractionRing R K] [IsFractionRing S L] in
/-- Commutativity of the fraction-field square transports embedded ring units. -/
theorem fieldUnits_map (u : Rˣ) :
    Units.map F.toMonoidHom (MilnorK.K2.DVR.fieldUnits R K u) =
      MilnorK.K2.DVR.fieldUnits S L (Units.map j.toMonoidHom u) := by
  apply Units.ext
  exact hF (u : R)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S]
  [IsDiscreteValuationRing S] in
/-- A uniformizer maps to the actual unit representing its image in the target DVR. -/
theorem uniformizer_map {π : R} (hπ : Irreducible π) (hjπ : Irreducible (j π)) :
    Units.map F.toMonoidHom (MilnorK.K2.DVR.uniformizer (K := K) hπ) =
      MilnorK.K2.DVR.uniformizer (K := L) hjπ := by
  apply Units.ext
  exact hF π

omit [IsDomain S] [IsDiscreteValuationRing S] in
/-- Transporting the original normalized-lift identity yields a target unit decomposition. -/
theorem mapped_normalizedLift_spec {π : R} (hπ : Irreducible π)
    (hjπ : Irreducible (j π)) (a : Kˣ) :
    MilnorK.K2.DVR.fieldUnits S L
        (Units.map j.toMonoidHom (MilnorK.K2.DVR.normalizedLift (K := K) hπ a)) =
      Units.map F.toMonoidHom a * MilnorK.K2.DVR.uniformizer (K := L) hjπ ^
        (-MilnorK.K2.DVR.value R K (Additive.ofMul a)) := by
  rw [← fieldUnits_map j F hF, MilnorK.K2.DVR.normalizedLift_spec]
  change Units.map F.toMonoidHom
    (a * MilnorK.K2.DVR.uniformizer (K := K) hπ ^
      (-MilnorK.K2.DVR.value R K (Additive.ofMul a))) = _
  rw [map_mul, map_zpow, uniformizer_map j F hF hπ hjπ]

/-- The normalized ring-unit lift forces preservation of integer order at index one. -/
theorem value_map {π : R} (hπ : Irreducible π) (hjπ : Irreducible (j π))
    (a : UnitsAdd K) :
    MilnorK.K2.DVR.value S L (unitsLinear F a) = MilnorK.K2.DVR.value R K a := by
  have h := congrArg (fun u : Lˣ => MilnorK.K2.DVR.value S L (Additive.ofMul u))
    (mapped_normalizedLift_spec j F hF hπ hjπ a.toMul)
  rw [MilnorK.K2.DVR.value_fieldUnits] at h
  change 0 = MilnorK.K2.DVR.value S L (Additive.ofMul
    (Units.map F.toMonoidHom a.toMul * MilnorK.K2.DVR.uniformizer (K := L) hjπ ^
      (-MilnorK.K2.DVR.value R K a))) at h
  simp only [ofMul_mul, ofMul_zpow, map_add, map_smul,
    MilnorK.K2.DVR.value_uniformizer, smul_eq_mul, mul_one] at h
  exact (eq_neg_of_add_eq_zero_left h.symm).trans (neg_neg _)

/-- Uniqueness of fraction-field lifts identifies the actual normalized ring units. -/
theorem normalizedLift_map {π : R} (hπ : Irreducible π)
    (hjπ : Irreducible (j π)) (a : Kˣ) :
    MilnorK.K2.DVR.normalizedLift (K := L) hjπ (Units.map F.toMonoidHom a) =
      Units.map j.toMonoidHom (MilnorK.K2.DVR.normalizedLift (K := K) hπ a) := by
  apply MilnorK.K2.DVR.fieldUnits_injective S L
  rw [MilnorK.K2.DVR.normalizedLift_spec, mapped_normalizedLift_spec j F hF hπ hjπ]
  change Units.map F.toMonoidHom a * MilnorK.K2.DVR.uniformizer (K := L) hjπ ^
    (-MilnorK.K2.DVR.value S L (unitsLinear F (Additive.ofMul a))) = _
  rw [value_map j F hF hπ hjπ]

variable [IsLocalHom j]

/-- Reducing those equal ring units gives compatibility of actual angular components. -/
theorem unitResidue_map {π : R} (hπ : Irreducible π)
    (hjπ : Irreducible (j π)) (a : Kˣ) :
    MilnorK.K2.DVR.unitResidue (K := L) hjπ (Units.map F.toMonoidHom a) =
      Units.map (residueFieldMap j).toMonoidHom
        (MilnorK.K2.DVR.unitResidue (K := K) hπ a) := by
  change Units.map (IsLocalRing.residue S).toMonoidHom
    (MilnorK.K2.DVR.normalizedLift (K := L) hjπ (Units.map F.toMonoidHom a)) = _
  rw [normalizedLift_map j F hF hπ hjπ]
  apply Units.ext
  exact (residueFieldMap_residue j _).symm

/-- Additive angular-component compatibility, with both sides derived from the DVRs. -/
theorem unitPart_map {π : R} (hπ : Irreducible π)
    (hjπ : Irreducible (j π)) (a : UnitsAdd K) :
    MilnorK.K2.DVR.unitPart (K := L) hjπ (unitsLinear F a) =
      unitsLinear (residueFieldMap j) (MilnorK.K2.DVR.unitPart (K := K) hπ a) := by
  exact congrArg Additive.ofMul (unitResidue_map j F hF hπ hjπ a.toMul)

/-- Unramified restriction commutes with the full actual degree-three residue map. -/
theorem residue_restrict {π : R} (hπ : Irreducible π)
    (hjπ : Irreducible (j π)) :
    (MilnorK.K2.map (residueFieldMap j)).comp (residue R K) =
      (residue S L).comp (MilnorK.K3.map F) := by
  apply MilnorK.K3.linearMap_ext
  intro a b c
  simp only [LinearMap.comp_apply, map_symbol3]
  rw [residue_eq hπ, residue_eq hjπ]
  change MilnorK.K2.map (residueFieldMap j)
    (residue3 (MilnorK.K2.DVR.data hπ) (MilnorK.K2.DVR.unitReductionCompatible hπ)
      (symbol3 a b c)) =
    residue3 (MilnorK.K2.DVR.data hjπ) (MilnorK.K2.DVR.unitReductionCompatible hjπ)
      (symbol3 (Units.map F.toMonoidHom a) (Units.map F.toMonoidHom b)
        (Units.map F.toMonoidHom c))
  simp only [residue3_symbol, residue3Bilinear_symbol, rawTame, MilnorK.K2.DVR.data]
  have hv (x : Kˣ) :
      MilnorK.K2.DVR.value S L (Additive.ofMul (Units.map F.toMonoidHom x)) =
        MilnorK.K2.DVR.value R K (Additive.ofMul x) :=
    value_map j F hF hπ hjπ (Additive.ofMul x)
  have hu (x : Kˣ) :
      MilnorK.K2.DVR.unitPart (K := L) hjπ (Additive.ofMul (Units.map F.toMonoidHom x)) =
        unitsLinear (residueFieldMap j)
          (MilnorK.K2.DVR.unitPart (K := K) hπ (Additive.ofMul x)) :=
    unitPart_map j F hF hπ hjπ (Additive.ofMul x)
  simp only [hv, hu, map_add, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, map_symbolBilinear, unitsLinear_residueSign]

end MilnorK.K3.DVR
