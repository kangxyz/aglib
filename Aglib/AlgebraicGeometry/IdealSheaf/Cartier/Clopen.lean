/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.Modules.Zariski
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Basic
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.UnitPower

/-! The original Cartier divisor extends across an open and closed immersion. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The original composite with a clopen immersion is effective Cartier.
Its actual ideal restricts to the given ideal and to the unit on the complement. -/
theorem isEffectiveCartier_comp_clopen {D U X : Scheme.{u}}
    (i : D ⟶ U) (j : U ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j]
    (hi : IsEffectiveCartier i) : IsEffectiveCartier (i ≫ j) := by
  let : IsClosedImmersion i := hi.isClosedImmersion
  refine ⟨inferInstance, ?_⟩
  let M := idealModule (i ≫ j)
  let W : X.Opens := ⟨(Set.range j)ᶜ, j.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let V (b : ULift.{u} Bool) : X.Opens := if b.down then j.opensRange else W
  have hV : TopologicalSpace.IsOpenCover V := by
    apply top_le_iff.mp
    intro x _
    by_cases hx : x ∈ Set.range j
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨true⟩, by simpa [V] using hx⟩
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨false⟩, by simpa [V, W] using hx⟩
  refine isLocallyRankOne_of_cover_restrict M V hV ?_
  rintro ⟨b⟩
  cases b
  · change IsLocallyRankOne W.toScheme (M.restrict W.ι)
    have hd : Disjoint (Set.range (i ≫ j)) (Set.range W.ι) := by
      apply Set.disjoint_left.mpr
      rintro _ ⟨d, rfl⟩ hd
      rw [Scheme.Opens.range_ι] at hd
      exact hd ⟨i d, rfl⟩
    have hW := isLocallyRankOne_of_iso W.toScheme
      (idealModulePullbackIsoOfDisjoint (i ≫ j) W.ι hd).symm
      (UnitPower.unitLineBundle W.toScheme).property
    exact isLocallyRankOne_of_iso _ ((restrictFunctorIsoPullback W.ι).app M).symm hW
  · change IsLocallyRankOne j.opensRange.toScheme (M.restrict j.opensRange.ι)
    have hU := isLocallyRankOne_of_iso U (idealModulePullbackFactor i j).symm hi.isLocallyRankOne
    exact isLocallyRankOne_of_iso _ (restrictOpensRangeIso j M).symm
      (pullback_locallyRankOne j.isoOpensRange.inv _ hU)

end AlgebraicGeometry.Scheme.Hom
