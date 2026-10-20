/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.DiscreteValuationRing.FractionAway
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Étale local DVR maps, valuations and fraction fields

Qualified declaration names and the stated theorem premises are retained from
the original unramified-descent source. This object module supplies the
corresponding construction; library placement adds no mathematical conclusion.
-/

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/DiscreteValuationRing/EtaleBaseChange.lean` at
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`834aa76d461f80797a21279c04a889cb0005275058455d6a1239ccae2e5d16a3`.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! ## Intrinsic normalized valuation preservation for actual unramified DVR maps -/

open IsDiscreteValuationRing
universe u
namespace IsDiscreteValuationRing
variable {R S : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
/-- Intrinsic ramification-index-one normalization: a map taking one actual
uniformizer to an actual uniformizer preserves the normalized valuations. -/
theorem addVal_map_of_uniformizer (f : R →+* S) {π : R}
    (hπ : Irreducible π) (hfπ : Irreducible (f π)) (r : R) :
    addVal S (f r) = addVal R r := by
  by_cases hr : r = 0
  · simp [hr]
  obtain ⟨n, hn⟩ := associated_pow_irreducible hr hπ
  have hm : Associated (f r) ((f π) ^ n) := by
    simpa using hn.map f.toMonoidHom
  calc
    addVal S (f r) = addVal S ((f π) ^ n) := (addVal_eq_iff_associated _ _).2 hm
    _ = n := hfπ.addVal_pow n
    _ = addVal R (π ^ n) := (hπ.addVal_pow n).symm
    _ = addVal R r := ((addVal_eq_iff_associated _ _).2 hn).symm

variable [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]

/-- Actual unramified local DVR maps carry a uniformizer to a uniformizer,
using the established maximal-ideal extension theorem. -/
theorem unramified_map_uniformizer {π : R} (hπ : Irreducible π) :
    Irreducible (algebraMap R S π) := by
  apply (irreducible_iff_uniformizer _).2
  rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S),
    hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]

/-- Normalized valuations are preserved by the actual unramified local map. -/
theorem unramified_addVal (r : R) :
    addVal S (algebraMap R S r) = addVal R r := by
  obtain ⟨π, hπ⟩ := exists_irreducible R
  exact addVal_map_of_uniformizer (algebraMap R S) hπ (unramified_map_uniformizer hπ) r
end IsDiscreteValuationRing

/- F3 source: EtaleFractionField.lean; SHA256
7ba52f597ac3c56467d5e801ce8f2c2d6c4aba1b02ac2dcabf080b4b8da534be. -/
section F3_EtaleFractionField

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped nonZeroDivisors
namespace IsDiscreteValuationRing.EtaleBaseChange
variable {R S F : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)] [Algebra.Etale R S]
  [Field F] [Algebra R F] [IsFractionRing R F]

local instance : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The actual fraction-field embedding induced by the finite étale ring map. -/
def fractionEmbedding : F →+* FractionRing S :=
  IsFractionRing.lift (g := algebraMap R (FractionRing S))
    ((IsFractionRing.injective S (FractionRing S)).comp
      (FaithfulSMul.algebraMap_injective R S))

lemma fractionEmbedding_compatible :
    (fractionEmbedding (R := R) (S := S) (F := F)).comp (algebraMap R F) =
      (algebraMap S (FractionRing S)).comp (algebraMap R S) := by
  ext r
  exact IsFractionRing.lift_algebraMap (A := R) (K := F)
    (g := algebraMap R (FractionRing S))
    ((IsFractionRing.injective S (FractionRing S)).comp
      (FaithfulSMul.algebraMap_injective R S)) r

/-- The induced F-algebra structure on the actual fraction field of S. -/
@[instance_reducible]
def fractionAlgebra : Algebra F (FractionRing S) :=
  (fractionEmbedding (R := R) (S := S) (F := F)).toAlgebra

lemma fractionAlgebra_tower :
    letI := fractionAlgebra (R := R) (S := S) (F := F)
    IsScalarTower R F (FractionRing S) := by
  let := fractionAlgebra (R := R) (S := S) (F := F)
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact (IsFractionRing.lift_algebraMap (A := R) (K := F)
    (g := algebraMap R (FractionRing S))
    ((IsFractionRing.injective S (FractionRing S)).comp
      (FaithfulSMul.algebraMap_injective R S)) r).symm

lemma fractionAlgebra_finite [Module.Finite R S] :
    letI := fractionAlgebra (R := R) (S := S) (F := F)
    Module.Finite F (FractionRing S) := by
  let := fractionAlgebra (R := R) (S := S) (F := F)
  let := fractionAlgebra_tower (R := R) (S := S) (F := F)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let : IsLocalization.Away π F :=
    IsDiscreteValuationRing.isLocalizationAway_of_nonzero_nonunit F hπ.ne_zero hπ.not_isUnit
  let : IsLocalization.Away (algebraMap R S π) (FractionRing S) :=
    IsDiscreteValuationRing.isLocalizationAway_of_nonzero_nonunit (FractionRing S)
      (IsDiscreteValuationRing.unramified_map_uniformizer hπ).ne_zero
      (IsDiscreteValuationRing.unramified_map_uniformizer hπ).not_isUnit
  have he : Algebra.algebraMapSubmonoid S (Submonoid.powers π) =
      Submonoid.powers (algebraMap R S π) := by
    exact Submonoid.map_powers (algebraMap R S) π
  let : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers π)) (FractionRing S) := by
    rw [he]
    infer_instance
  exact Module.Finite.of_isLocalization R S (Submonoid.powers π)

end IsDiscreteValuationRing.EtaleBaseChange

end -- closes the source module's noncomputable section
end F3_EtaleFractionField

end
