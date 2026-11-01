/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange
public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic

/-! # Integral and normal original stalk-spectrum base changes

The actual pullback of an integral dominant map along a flat preimmersion
containing the generic point is integral. Its original projection induces
isomorphisms on stalks, so normal stalks are retained as well. The sole proof
from Finite/Birational/NormalLocus is generalized here; the original stalk
specialization is a thin consumer.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- A flat preimmersion whose image contains the original generic point
retains integrality of an integral scheme dominant over the integral base. -/
theorem isIntegral_pullback_of_flat_preimmersion
    {Y X T : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (p : Y ⟶ X) [IsDominant p] (s : T ⟶ X) [Flat s] [IsPreimmersion s]
    (hg : genericPoint X ∈ Set.range s) : IsIntegral (pullback p s) := by
  let a := pullback.fst p s
  let (z : (pullback p s : Scheme.{u})) :
      IsDomain ((pullback p s).presheaf.stalk z) := by
    let : IsIso (a.stalkMap z) :=
      Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks a z
    exact (asIso (a.stalkMap z)).commRingCatIsoToRingEquiv.symm.toMulEquiv.isDomain _
  let : IsReduced (pullback p s) := isReduced_of_isReduced_stalk _
  obtain ⟨t, ht⟩ := hg
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback (genericPoint Y) t
    ((Scheme.map_genericPoint_of_isDominant Y p).trans ht.symm)
  have hgeneric : IsGenericPoint z (Set.univ : Set (pullback p s : Scheme.{u})) := by
    apply isGenericPoint_iff_specializes.mpr
    intro w
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    apply a.isEmbedding.isInducing.specializes_iff.mp
    change pullback.fst p s z ⤳ pullback.fst p s w
    rw [hz]
    exact (genericPoint_spec Y).specializes trivial
  let : IrreducibleSpace (pullback p s : Scheme.{u}) :=
    (irreducibleSpace_def _).mpr hgeneric.isIrreducible
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The unchanged projection of a flat preimmersion base change preserves
normality through its actual stalk-map isomorphism. -/
theorem normalStalks_pullback_of_flat_preimmersion
    {Y X T : Scheme.{u}} (p : Y ⟶ X) (s : T ⟶ X) [Flat s] [IsPreimmersion s]
    (hY : NormalStalks Y) : NormalStalks (pullback p s) := by
  intro z
  let a := pullback.fst p s
  let : IsIso (a.stalkMap z) := Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks a z
  let : IsDomain (Y.presheaf.stalk (a z)) := (hY (a z)).1
  let : IsIntegrallyClosed (Y.presheaf.stalk (a z)) := (hY (a z)).2
  let e := (asIso (a.stalkMap z)).commRingCatIsoToRingEquiv
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

/-- The original stalk-spectrum specialization uses the same integral
pullback construction and its actual generic-point image. -/
theorem isIntegral_pullback_fromSpecStalk
    {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (p : Y ⟶ X) [IsDominant p] (x : X) :
    IsIntegral (pullback p (X.fromSpecStalk x)) := by
  let : Flat (X.fromSpecStalk x) := Scheme.fromSpecStalk_flat X x
  apply isIntegral_pullback_of_flat_preimmersion p (X.fromSpecStalk x)
  rw [Scheme.range_fromSpecStalk]
  exact (genericPoint_spec X).specializes trivial

/-- Normality on the original stalk-spectrum pullback is the same
flat-preimmersion stalk-map transfer. -/
theorem normalStalks_pullback_fromSpecStalk
    {Y X : Scheme.{u}} (p : Y ⟶ X) (x : X) (hY : NormalStalks Y) :
    NormalStalks (pullback p (X.fromSpecStalk x)) := by
  let : Flat (X.fromSpecStalk x) := Scheme.fromSpecStalk_flat X x
  exact normalStalks_pullback_of_flat_preimmersion p (X.fromSpecStalk x) hY

end AlgebraicGeometry.Scheme
