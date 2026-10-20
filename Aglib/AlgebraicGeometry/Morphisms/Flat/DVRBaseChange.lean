/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.GenericFiber
public import Aglib.RingTheory.DiscreteValuationRing.FractionAway
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Flat ring base maps and compatible DVR generic fibres

Faithful flatness gives flatness and surjectivity of the native spectrum scalar
map. A DVR fraction map is an open immersion. An injective local map of DVRs
and a compatible fraction-field map give the actual cartesian square, including
ramified maps; no ramification-index restriction is imposed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Spec

/-- Faithful flatness of the specified algebra makes its spectrum map flat and surjective. -/
theorem algebraMap_flat_surjective {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Module.FaithfullyFlat R S] :
    Flat (Spec.algebraMap R S) ∧ Surjective (Spec.algebraMap R S) := by
  apply (flat_and_surjective_SpecMap_iff _).mpr
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance

end AlgebraicGeometry.Spec

namespace AlgebraicGeometry.Scheme.LocalRing.GenericFiber

variable {R F : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- The canonical generic map is the principal open immersion of a DVR.
No smoothness or generic-pullback conclusion is supplied as an input. -/
instance baseMap_openImmersion : IsOpenImmersion (baseMap R F) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let := IsDiscreteValuationRing.isLocalizationAway_of_nonzero_nonunit F hπ.ne_zero hπ.not_isUnit
  exact IsOpenImmersion.of_isLocalization π


variable {S K : Type u} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Algebra S K] [IsFractionRing S K]

/-- The canonical ring/field square is cartesian for an injective local DVR
map and a compatible fraction-field map, independently of ramification index. -/
theorem dvr_isPullback (f : R →+* S) [IsLocalHom f]
    (hf : Function.Injective f) (embedding : F →+* K)
    (h : embedding.comp (algebraMap R F) = (algebraMap S K).comp f) :
    IsPullback (baseMap S K) (Spec.map (CommRingCat.ofHom embedding))
      (Spec.map (CommRingCat.ofHom f)) (baseMap R F) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let := IsDiscreteValuationRing.isLocalizationAway_of_nonzero_nonunit F hπ.ne_zero hπ.not_isUnit
  let := IsDiscreteValuationRing.isLocalizationAway_of_nonzero_nonunit K
    (show f π ≠ 0 from fun h => hπ.ne_zero (hf (h.trans f.map_zero.symm)))
    (fun hu => hπ.not_isUnit ((isUnit_map_iff f π).mp hu))
  exact isPullback_SpecMap_of_isPushout
    (CommRingCat.ofHom f) (CommRingCat.ofHom (algebraMap R F))
    (CommRingCat.ofHom (algebraMap S K)) (CommRingCat.ofHom embedding)
    (CommRingCat.isPushout_of_isLocalization f embedding h (Submonoid.powers π))
end AlgebraicGeometry.Scheme.LocalRing.GenericFiber

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/Morphisms/Flat/DVRBaseChange.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 6c46c7ac8178ac43dd801dc593be078b5f4730a9eee6d3d2e1372124da09994f. -/
