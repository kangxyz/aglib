/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.BaseChange.Stalk
public import Aglib.AlgebraicGeometry.Morphisms.IsIso.StalkBaseChange

/-!
# Relative normalization under flat preimmersions

Flatness together with the actual preimmersion makes the original stalk
homomorphisms isomorphisms. Pasting the original normalization comparisons
and testing the integral comparison on local spectra proves the result.
This is not an arbitrary flat-normality or algebraization assertion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The original relative-normalization comparison is invertible under a
flat preimmersion. In particular it applies to model localizations obtained
by base-changing an original `fromSpecStalk`, without identifying the model
localization with one of its own stalk spectra. -/
theorem normalizationPullback_isIso_of_flat_preimmersion
    {X S Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] [IsPreimmersion g] :
    IsIso (f.normalizationPullback g) := by
  let n := f.normalizationPullback g
  let b := pullback.snd f.fromNormalization g
  let p := pullback.snd f g
  apply Scheme.isIso_of_isClosedMap_of_baseStalkPullback n b n.isClosedMap
  intro y
  let c := Y.fromSpecStalk y
  let : IsIso (p.normalizationPullback c) := normalizationPullback_isIso_fromSpecStalk p y
  let : IsIso (g.stalkMap y) :=
    Scheme.Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks g y
  let d := S.fromSpecStalk (g y)
  let k := Spec.map (g.stalkMap y)
  let : IsIso k := inferInstance
  let : IsIso (f.normalizationPullback d) := normalizationPullback_isIso_fromSpecStalk f (g y)
  let : IsIso ((pullback.snd f d).normalizationPullback k) := inferInstance
  have hcomp : IsIso (f.normalizationPullback (c ≫ g)) := by
    have H := normalizationPullback_isIso_comp f d k
    have hkd : k ≫ d = c ≫ g := Scheme.SpecMap_stalkMap_fromSpecStalk g (x := y)
    rw [hkd] at H
    exact H
  let := hcomp
  have hk := normalizationPullback_isIso_baseChange_of_comp f g c
  exact Scheme.isIso_pullback_snd_of_overBaseChange n b p.fromNormalization
    (f.normalizationPullback_snd g) c hk

end AlgebraicGeometry.Scheme.Hom
