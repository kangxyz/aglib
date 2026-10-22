/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.IdealMap
public import Aglib.RingTheory.AdicCompletion.DiscreteValuationRing
public import Aglib.RingTheory.DiscreteValuationRing.SameUniformizer

/-! # Completion of an actual same-uniformizer map of DVRs -/

@[expose] public noncomputable section

open IsLocalRing

namespace AdicCompletion

universe u v
variable {R : Type u} {S : Type v}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  (f : R →+* S) (p : R) (hp : Irreducible p) (hfp : Irreducible (f p))

/-- Same-uniformizer completion uses the maximal-ideal quotient maps. -/
def sameUniformizerMap :
    AdicCompletion (maximalIdeal R) R →+* AdicCompletion (maximalIdeal S) S :=
  idealMap f (maximalIdeal R) (maximalIdeal S)
    (IsDiscreteValuationRing.map_maximalIdeal_of_map_irreducible f hp hfp)

@[simp] theorem sameUniformizerMap_algebraMap (r : R) :
    sameUniformizerMap f p hp hfp
        (algebraMap R (AdicCompletion (maximalIdeal R) R) r) =
      algebraMap S (AdicCompletion (maximalIdeal S) S) (f r) :=
  idealMap_algebraMap _ _ _ _ r

/-- Injectivity is proved by DVR decomposition, not by an exactness claim about completion. -/
theorem sameUniformizerMap_injective :
    Function.Injective (sameUniformizerMap f p hp hfp) := by
  apply IsDiscreteValuationRing.injective_of_map_irreducible
    (sameUniformizerMap f p hp hfp) (irreducible_algebraMap R p hp)
  rw [sameUniformizerMap_algebraMap]
  exact irreducible_algebraMap S (f p) hfp

/-- The completed map is local because it sends the actual uniformizer to a uniformizer. -/
theorem sameUniformizerMap_isLocalHom :
    IsLocalHom (sameUniformizerMap f p hp hfp) := by
  apply IsDiscreteValuationRing.isLocalHom_of_map_irreducible
    (sameUniformizerMap f p hp hfp) (irreducible_algebraMap R p hp)
  rw [sameUniformizerMap_algebraMap]
  exact irreducible_algebraMap S (f p) hfp

/-- The native residue equivalences commute with the actual completed map. -/
theorem residueFieldEquiv_sameUniformizerMap
    (x : ResidueField (AdicCompletion (maximalIdeal R) R)) :
    letI : IsLocalHom f :=
      IsDiscreteValuationRing.isLocalHom_of_map_irreducible f hp hfp
    letI : IsLocalHom (sameUniformizerMap f p hp hfp) :=
      sameUniformizerMap_isLocalHom f p hp hfp
    residueFieldEquiv S (ResidueField.map (sameUniformizerMap f p hp hfp) x) =
      ResidueField.map f (residueFieldEquiv R x) := by
  let : IsLocalHom f :=
    IsDiscreteValuationRing.isLocalHom_of_map_irreducible f hp hfp
  let : IsLocalHom (sameUniformizerMap f p hp hfp) :=
    sameUniformizerMap_isLocalHom f p hp hfp
  change residueFieldEquiv S (ResidueField.map (sameUniformizerMap f p hp hfp) x) =
    ResidueField.map f (residueFieldEquiv R x)
  obtain ⟨y, rfl⟩ := (residueField_map_bijective R).2 x
  obtain ⟨r, rfl⟩ := residue_surjective y
  rw [residueFieldEquiv_map]
  rw [ResidueField.map_residue, ResidueField.map_residue,
    sameUniformizerMap_algebraMap, ← ResidueField.map_residue,
    residueFieldEquiv_map]
  exact (ResidueField.map_residue f r).symm

/-- Extension to the actual fraction fields. -/
def sameUniformizerFractionMap :
    FractionRing (AdicCompletion (maximalIdeal R) R) →+*
      FractionRing (AdicCompletion (maximalIdeal S) S) :=
  IsFractionRing.lift
    (g := (algebraMap (AdicCompletion (maximalIdeal S) S)
      (FractionRing (AdicCompletion (maximalIdeal S) S))).comp
        (sameUniformizerMap f p hp hfp))
    ((IsFractionRing.injective _ _).comp (sameUniformizerMap_injective f p hp hfp))

@[simp] theorem sameUniformizerFractionMap_algebraMap
    (x : AdicCompletion (maximalIdeal R) R) :
    sameUniformizerFractionMap f p hp hfp
        (algebraMap _ (FractionRing (AdicCompletion (maximalIdeal R) R)) x) =
      algebraMap _ (FractionRing (AdicCompletion (maximalIdeal S) S))
        (sameUniformizerMap f p hp hfp x) :=
  IsFractionRing.lift_algebraMap _ x

end AdicCompletion
