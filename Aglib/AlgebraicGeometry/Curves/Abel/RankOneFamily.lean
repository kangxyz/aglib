/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.RankOneOpen
public import Aglib.AlgebraicGeometry.Cohomology.Vanishing.Noetherian
public import Aglib.AlgebraicGeometry.Curves.Abel.ZeroDivisor
public import Aglib.AlgebraicGeometry.Modules.Invertible.RelativeFlat
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Basic
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Dimension
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality
public import Aglib.AlgebraicGeometry.Properties.Normal.Components
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.FinitePresentation

/-!
# Canonical evaluation on the rank-one locus of a relative curve

Every actual residue-field fibre of a proper smooth relative curve with
geometrically connected fibres is a native `Curve.Properties` curve. Its
Noetherian dimension-one vanishing discharges the amplitude hypothesis of
the general rank-one-open theorem. On that original open, pull back the
given line bundle and use the existing direct-image/evaluation contraction.

The native fibrewise regularity and relative-Cartier locality theorems show
that its actual zero subscheme is effective Cartier, finite, flat, and
locally finitely presented over the open. The zero scheme may be empty;
neither positive degree nor nonemptiness is asserted. No Picard scheme,
Jacobian, origin, or polarization data occur in this construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme Scheme.Cohomology Scheme.Modules Scheme.Modules.Invertible
open Scheme.Modules.QuasiCoherent Scheme.Modules.Hom

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel

local instance : MorphismProperty.IsStableUnderBaseChange
    (@SmoothOfRelativeDimension.{u} 1) :=
  smoothOfRelativeDimension_isStableUnderBaseChange 1

variable {Z S : Scheme.{u}} (f : Z ⟶ S)
  [IsProper f] [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]

local instance : Smooth f := SmoothOfRelativeDimension.smooth 1 f

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual field fibre, for every field point, is the native proper
smooth geometrically connected curve. -/
theorem rankOneFamily_fibre_properties (K : Type u) [Field K]
    (t : Spec (.of K) ⟶ S) : Properties (Over.mk (pullback.snd f t)) := by
  refine ⟨?_, ?_, ?_⟩
  · change SmoothOfRelativeDimension 1 (pullback.snd f t)
    exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension.{u} 1) f t inferInstance
  · change IsProper (pullback.snd f t)
    infer_instance
  · change GeometricallyConnected (pullback.snd f t)
    infer_instance

-- The native point fibre is the original residue-field pullback.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual fibre cohomology vanishes above degree one. This applies to every
module sheaf; coherence is not needed for this dimension-vanishing step. -/
theorem rankOneFamily_pointFiber_vanishing (M : Z.Modules) (s : S) (q : ℕ) (hq : 1 < q) :
    Subsingleton (modulePointFiberCohomology f M q s) := by
  let Y : FScheme (S.residueField s) := Over.mk (f.fiberToSpecResidueField s)
  have hY : Properties Y := rankOneFamily_fibre_properties f _ (S.fromSpecResidueField s)
  have : IsNoetherian (f.fiber s) := curveProperties_isNoetherian hY
  exact noetherianSheafCohomology_vanishing (f.fiber s)
    (moduleAddSheaf _ ((Scheme.Modules.pullback (f.fiberι s)).obj M)) 1 q
    (curveProperties_dimension smoothFieldDimension hY).le hq

variable [IsLocallyNoetherian S] (L : LineBundle Z)

/-- The actual rank-one open of the original line-bundle family. -/
def rankOneOpen : S.Opens :=
  modulePointFiberRankOneOpen f L.val
    (by
      have := lineBundle_isFinitePresentation Z L
      exact affineLocallyFiniteType_of_finitePresentation L.val)
    (relativeFlat_of_flat f L) (rankOneFamily_pointFiber_vanishing f L.val)

/-- Membership retains the original fibre cohomology, including its scalar
action, and actual positive-degree vanishing. -/
theorem mem_rankOneOpen (s : S) :
    s ∈ rankOneOpen f L ↔ modulePointFiberCohomologyDimension f L.val 0 s = 1 ∧
      ∀ q : ℕ, 0 < q → Subsingleton (modulePointFiberCohomology f L.val q s) := Iff.rfl

/-- The original line bundle pulled back along the canonical open family. -/
abbrev rankOneBundle : LineBundle (pullback f (rankOneOpen f L).ι) :=
  pullbackLineBundle (pullback.fst f (rankOneOpen f L).ι) L

/-- The native geometric concentration hypothesis is now proved on the
original open, with no cohomological hypothesis left for the consumer. -/
theorem rankOneConcentration :
    FibreCohomologyConcentrated (pullback.snd f (rankOneOpen f L).ι)
      (rankOneBundle f L).val 1 := by
  have := lineBundle_isLocallyFree Z L
  have : L.val.IsQuasicoherent := inferInstance
  exact fibreCohomologyConcentrated_rankOneOpen f L.val
    (by
      have := lineBundle_isFinitePresentation Z L
      exact affineLocallyFiniteType_of_finitePresentation L.val)
    (relativeFlat_of_flat f L) (rankOneFamily_pointFiber_vanishing f L.val)

/-- The actual canonical evaluation contraction on the rank-one open. -/
def rankOneEvaluation :
    (evaluationIdealLineBundle (pullback.snd f (rankOneOpen f L).ι)
      (rankOneBundle f L) (rankOneConcentration f L)).val ⟶
        (show (pullback f (rankOneOpen f L).ι).Modules from
          SheafOfModules.unit (pullback f (rankOneOpen f L).ι).ringCatSheaf) :=
  evaluationContraction (pullback.snd f (rankOneOpen f L).ι)
    (rankOneBundle f L) (rankOneConcentration f L)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Canonical evaluation is a monomorphism; all native fibre-regularity
suppliers are discharged for the same original curve family. -/
theorem mono_rankOneEvaluation : Mono (rankOneEvaluation f L) := by
  let p := pullback.snd f (rankOneOpen f L).ι
  have : SmoothOfRelativeDimension 1 p := MorphismProperty.pullback_snd _ _ inferInstance
  let B := rankOneBundle f L
  let hB := rankOneConcentration f L
  have hr := evaluationContraction_geometric_regular p B hB
    smoothFieldNormality normalComponentsOpen (fun K _ _ t =>
      rankOneFamily_fibre_properties p K t)
  exact (fibrewiseRegularLineBundle _ _ p (evaluationIdealLineBundle p B hB)
    (evaluationContraction p B hB) inferInstance inferInstance hr).1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same actual evaluation zero scheme is finite flat and locally
finitely presented over the rank-one open, with empty fibres allowed. -/
theorem rankOneEvaluation_finite_flat :
    IsFinite (zeroInclusion (rankOneEvaluation f L) ≫ pullback.snd f (rankOneOpen f L).ι) ∧
      Flat (zeroInclusion (rankOneEvaluation f L) ≫ pullback.snd f (rankOneOpen f L).ι) ∧
      LocallyOfFinitePresentation
        (zeroInclusion (rankOneEvaluation f L) ≫ pullback.snd f (rankOneOpen f L).ι) := by
  let p := pullback.snd f (rankOneOpen f L).ι
  have : SmoothOfRelativeDimension 1 p := MorphismProperty.pullback_snd _ _ inferInstance
  exact evaluationZero_finite_flat smoothFieldNormality normalComponentsOpen
    fibrewiseRegularLineBundle smoothRelativeCartierLocality p
    (rankOneBundle f L) (rankOneConcentration f L) (fun K _ _ t =>
      rankOneFamily_fibre_properties p K t)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original evaluation zero immersion is a relative effective Cartier
divisor on the actual open family. -/
theorem rankOneEvaluation_isRelativeEffectiveCartier :
    Hom.IsRelativeEffectiveCartier (zeroInclusion (rankOneEvaluation f L))
      (pullback.snd f (rankOneOpen f L).ι) := by
  have : Mono (rankOneEvaluation f L) := mono_rankOneEvaluation f L
  exact {
    isClosedImmersion := zeroInclusion_isClosedImmersion _
    isLocallyRankOne := (zeroIdealLineBundle
      (evaluationIdealLineBundle (pullback.snd f (rankOneOpen f L).ι)
        (rankOneBundle f L) (rankOneConcentration f L)) (rankOneEvaluation f L)).property
    flat := (rankOneEvaluation_finite_flat f L).2.1 }

end AlgebraicGeometry.Scheme.OverField.Curve.Abel
