/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.LocalModification
public import Aglib.AlgebraicGeometry.Descent.CompletionPointBlowup

/-!
# Prescribed closed points on actual localized models

The local model is retained in its original cartesian square. Properness over
the local spectrum puts every closed point on its closed fibre. The embedding
and lifting properties of the model localization then show that its image is
closed on the global model. The actual residue-field square is cartesian.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.LocalModification

/-- A closed point of the proper local model maps to a closed point of the
global model over the original selected closed point. -/
theorem localizationClosedPoint_data {X S Y : Scheme.{u}}
    (x : X) (hx : IsClosed ({x} : Set X))
    (a : Y ⟶ S) (p : Y ⟶ Spec (X.presheaf.stalk x)) (f : S ⟶ X)
    (H : IsPullback a p f (X.fromSpecStalk x)) [IsProper p]
    (y : Y) (hy : IsClosed ({y} : Set Y)) :
    IsClosed ({a y} : Set S) ∧ f (a y) = x := by
  let : IsPreimmersion a := MorphismProperty.of_isPullback H.flip inferInstance
  have hpclosed : IsClosed ({p y} : Set (Spec (X.presheaf.stalk x))) := by
    simpa only [Set.image_singleton] using p.isClosedMap _ hy
  have hpy : p y = IsLocalRing.closedPoint (X.presheaf.stalk x) := by
    apply PrimeSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal (p y)).mp hpclosed)
  have hcenter : f (a y) = x := by
    have hw := congrArg (fun k : Y ⟶ X => k y) H.w
    simpa only [Scheme.Hom.comp_apply, hpy, Scheme.fromSpecStalk_closedPoint] using hw
  refine ⟨?_, hcenter⟩
  apply closure_subset_iff_isClosed.mp
  intro z hz
  have hs : a y ⤳ z := specializes_iff_mem_closure.mpr hz
  have hfz : f z = x := by
    have hz' := specializes_iff_mem_closure.mp (hs.map f.continuous)
    rw [hcenter, hx.closure_eq] at hz'
    exact Set.mem_singleton_iff.mp hz'
  obtain ⟨t, ht, _⟩ := exists_preimage_over_center x a p f H z hfz
  have hyt : y ⤳ t := a.isEmbedding.isInducing.specializes_iff.mp (ht.symm ▸ hs)
  have ht' := specializes_iff_mem_closure.mp hyt
  rw [hy.closure_eq] at ht'
  have hty : t = y := Set.mem_singleton_iff.mp ht'
  exact Set.mem_singleton_iff.mpr (ht.symm.trans (congrArg a hty))

/-- Flat preimmersions identify the original residue fields at every point. -/
theorem residueFieldMap_isIso_of_flat_preimmersion {Y X : Scheme.{u}}
    (g : Y ⟶ X) [Flat g] [IsPreimmersion g] (y : Y) :
    IsIso (g.residueFieldMap y) := by
  let : IsIso (g.stalkMap y) :=
    Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks g y
  exact (IsLocalRing.ResidueField.mapEquiv
    (asIso (g.stalkMap y)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom

/-- The full original residue-point square is cartesian under a flat
preimmersion; the point ideal comparison therefore uses the full point ideal. -/
theorem point_isPullback_of_flat_preimmersion {Y X : Scheme.{u}}
    (g : Y ⟶ X) [Flat g] [IsPreimmersion g] (y : Y) :
    IsPullback (Y.fromSpecResidueField y) (Spec.map (g.residueFieldMap y))
      g (X.fromSpecResidueField (g y)) := by
  let : IsIso (g.residueFieldMap y) := residueFieldMap_isIso_of_flat_preimmersion g y
  exact IsPullback.of_vert_isIso_mono
    ⟨(g.SpecMap_residueFieldMap_fromSpecResidueField y).symm⟩

/-- The full reduced point centre, not just its support, is preserved. -/
theorem pointCentre_comap_of_flat_preimmersion {Y X : Scheme.{u}}
    (g : Y ⟶ X) [Flat g] [IsPreimmersion g] (y : Y)
    (hx : IsClosed ({g y} : Set X)) :
    (X.fromSpecResidueField (g y)).ker.comap g = (Y.fromSpecResidueField y).ker :=
  Blowup.pointCentre_comap_of_isPullback g y hx (point_isPullback_of_flat_preimmersion g y)

end AlgebraicGeometry.Scheme.LocalModification
