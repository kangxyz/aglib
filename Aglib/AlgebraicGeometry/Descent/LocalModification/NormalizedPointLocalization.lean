/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.LocalModification.PointLocalization
public import Aglib.AlgebraicGeometry.Normalization.FunctionField.FlatPreimmersion
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.NormalizedPointBlowupChain
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# The prescribed normalized-point step under model localization

Both point centres and both generic normalizations are the original ones.
Finiteness of the global normalization is not inferred from this comparison;
that remains a separate properness/globalization obligation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- A nonempty flat source over an integral scheme meets the generic point,
since flatness lifts its generalization from any source point. -/
theorem isDominant_of_flat_of_nonempty {Y X : Scheme.{u}}
    [IsIntegral X] [Nonempty Y] (g : Y ⟶ X) [Flat g] : IsDominant g := by
  classical
  obtain ⟨y⟩ := ‹Nonempty Y›
  have hgeneric : genericPoint X ∈ Set.range g :=
    (Flat.generalizingMap g).stableUnderGeneralization_range
      ((genericPoint_spec X).specializes (y := g y) trivial) ⟨y, rfl⟩
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff, ← (genericPoint_spec X).def]
  exact closure_mono (Set.singleton_subset_iff.mpr hgeneric)

namespace Blowup

/-- The whole original normalized point blowup, not just its ordinary blowup,
commutes with a flat preimmersion. The image centre is assumed closed and
nongeneric exactly where the lower normalized-point construction requires it. -/
def normalizedPointLocalizationIso
    {Y X : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (g : Y ⟶ X) [Flat g] [IsPreimmersion g]
    (y : Y) (hy : IsClosed ({y} : Set Y)) (hyne : y ≠ genericPoint Y)
    (hx : IsClosed ({g y} : Set X)) (hxne : g y ≠ genericPoint X) :
    normalizedPointBlowup Y y hy hyne ≅
      pullback (normalizedPointBlowupMap X (g y) hx hxne) g := by
  let BX := blowupDatum (X.fromSpecResidueField (g y)).ker
  let BY := blowupDatum (Y.fromSpecResidueField y).ker
  let : IsIntegral BX.Y := pointBlowup_isIntegral X (g y) hx hxne
  let : IsIntegral BY.Y := pointBlowup_isIntegral Y y hy hyne
  let hI := LocalModification.pointCentre_comap_of_flat_preimmersion g y hx
  let b := BaseChange.map g hI BX BY
  have H : IsPullback b BY.map BX.map g :=
    BaseChange.isPullback blowupFlatBaseChange g inferInstance hI BX BY
  let : Flat b := MorphismProperty.of_isPullback H.flip inferInstance
  let : IsPreimmersion b := MorphismProperty.of_isPullback H.flip inferInstance
  let : IsDominant b := isDominant_of_flat_of_nonempty b
  let νX := (BX.Y.fromSpecStalk (genericPoint BX.Y)).fromNormalization
  let νY := (BY.Y.fromSpecStalk (genericPoint BY.Y)).fromNormalization
  let E := genericNormalizationPullbackIso b
  have HE : IsPullback (E.hom ≫ pullback.fst νX b) νY νX b := by
    apply (IsPullback.of_hasPullback νX b).of_iso' E (.refl _) (.refl _) (.refl _)
    · simp
    · simp [E, νY, νX]
    · simp
    · simp
  exact (HE.paste_vert H).isoPullback

@[reassoc (attr := simp)]
theorem normalizedPointLocalizationIso_hom_snd
    {Y X : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (g : Y ⟶ X) [Flat g] [IsPreimmersion g]
    (y : Y) (hy : IsClosed ({y} : Set Y)) (hyne : y ≠ genericPoint Y)
    (hx : IsClosed ({g y} : Set X)) (hxne : g y ≠ genericPoint X) :
    (normalizedPointLocalizationIso g y hy hyne hx hxne).hom ≫
      pullback.snd (normalizedPointBlowupMap X (g y) hx hxne) g =
      normalizedPointBlowupMap Y y hy hyne := by
  simp [normalizedPointLocalizationIso, normalizedPointBlowupMap]

/-- The original lower projection commutes with the original blowdown map. -/
@[reassoc]
theorem normalizedPointLocalizationIso_hom_fst_comp
    {Y X : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (g : Y ⟶ X) [Flat g] [IsPreimmersion g]
    (y : Y) (hy : IsClosed ({y} : Set Y)) (hyne : y ≠ genericPoint Y)
    (hx : IsClosed ({g y} : Set X)) (hxne : g y ≠ genericPoint X) :
    (normalizedPointLocalizationIso g y hy hyne hx hxne).hom ≫
      pullback.fst (normalizedPointBlowupMap X (g y) hx hxne) g ≫
        normalizedPointBlowupMap X (g y) hx hxne =
      normalizedPointBlowupMap Y y hy hyne ≫ g := by
  rw [pullback.condition, ← Category.assoc, normalizedPointLocalizationIso_hom_snd]

end Blowup
end AlgebraicGeometry.Scheme
