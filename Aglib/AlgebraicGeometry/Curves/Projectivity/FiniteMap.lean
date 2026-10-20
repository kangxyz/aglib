/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Finite.Birational
public import Aglib.AlgebraicGeometry.Curves.Projectivity.FiniteLineModel
public import Aglib.AlgebraicGeometry.Curves.Core
public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Native
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Dimension
public import Aglib.AlgebraicGeometry.Properties.Normal.Components

/-!
# Finite projective-line maps from the original normal proper curve

The rational-graph construction is exported by `FiniteLineModel`. Normality of
the original target identifies that model with the original curve through the
actual finite map. Composing its inverse with the other finite graph projection
and the canonical two-chart/projective-line comparison retains the original
scheme, field, and structural morphism. The actual coordinate-reindexing
isomorphism then reaches native projective space with coordinates
`ULift.{u} (Fin 2)`, in the original field universe.

The original `PointedIsogenies.Properties` application uses the native
normality, open-components and dimension suppliers in Aglib revision
`197ca0728db3cdf1552a6bcefeeda901e3377862`. These are proved inputs, not extra
theorem-family parameters. The graph and line comparison are from R5 revision
`5b493a5709ba2e4242f94cf163611602c03f3cf3`.

A finite morphism to P1 is constructed here; the projective embedding theorem
and projectivity of nonnormal or nonreduced proper curves are separate results.
-/




@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart
open AlgebraicGeometry.Scheme

open CategoryTheory AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)
open AlgebraicGeometry.Scheme.OverField.Curve
open AlgebraicGeometry.Scheme.OverField.Curve.Projectivity

namespace AlgebraicGeometry.Scheme.OverField.Curve.Projectivity

universe u

variable {K : Type u} [Field K]

/-- The original normal integral proper dimension-one scheme has an actual
finite dominant map to the literal polynomial projective line, over its field. -/
theorem exists_finite_dominant_map_to_projectiveP1_of_normal
    (X : FScheme K) [IsIntegral X.left] [IsProper X.hom]
    (hN : Scheme.NormalStalks X.left) (hdim : topologicalKrullDim X.left = 1) :
    ∃ f : X ⟶ Over.mk (AlgebraicGeometry.Scheme.ProjectiveLine.structureMap K),
      IsFinite f.left ∧ IsDominant f.left := by
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : IsNoetherian X.left := ⟨⟩
  obtain ⟨Y, p, q, hY, hp, _, hq, hqdom, U, hU, hiso⟩ :=
    exists_finite_birational_twoChartLine_model X hdim
  let : IsIntegral Y.left := hY
  let : IsFinite p.left := hp
  let : IsFinite q.left := hq
  let : IsDominant q.left := hqdom
  let : Nonempty U.1 := hU
  let : IsIso (p.left ∣_ U.1) := hiso
  let e : Y ≅ X := Over.isoMk (Scheme.finiteBirationalIso p.left hN U.1) p.w
  let c := twoChartLineOverIsoProjectiveP1 K
  let : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  let : IsIso c.hom.left := inferInstanceAs (IsIso ((Over.forget _).map c.hom))
  refine ⟨e.inv ≫ q ≫ c.hom, ?_, ?_⟩
  · change IsFinite (e.inv.left ≫ q.left ≫ c.hom.left)
    infer_instance
  · change IsDominant (e.inv.left ≫ q.left ≫ c.hom.left)
    infer_instance

/-- The existing smooth proper geometrically connected curve hypotheses
supply all normality, integrality and dimension inputs to the original map. -/
theorem curveProperties_exists_finite_dominant_map_to_projectiveP1
    {X : FScheme K} (hX : Properties X) :
    ∃ f : X ⟶ Over.mk (AlgebraicGeometry.Scheme.ProjectiveLine.structureMap K),
      IsFinite f.left ∧ IsDominant f.left := by
  let : IsIntegral X.left :=
    curveProperties_isIntegral Scheme.smoothFieldNormality Scheme.normalComponentsOpen hX
  let : IsProper X.hom := hX.proper
  exact exists_finite_dominant_map_to_projectiveP1_of_normal X
    (Scheme.smoothFieldNormality K X.left X.hom (curveProperties_smooth hX))
    (curveProperties_dimension Scheme.smoothFieldDimension hX)

/-- The original normal integral proper curve maps finitely and dominantly to
native projective one-space in the unchanged field universe. -/
theorem exists_finite_dominant_map_to_nativeP1_of_normal
    (X : FScheme K) [IsIntegral X.left] [IsProper X.hom]
    (hN : Scheme.NormalStalks X.left) (hdim : topologicalKrullDim X.left = 1) :
    ∃ f : X ⟶ Over.mk
      (_root_.AlgebraicGeometry.ProjectiveSpace.toSpec K (ULift.{u} (Fin 2))),
      IsFinite f.left ∧ IsDominant f.left := by
  obtain ⟨f, hf, hdom⟩ := exists_finite_dominant_map_to_projectiveP1_of_normal X hN hdim
  let : IsFinite f.left := hf
  let : IsDominant f.left := hdom
  let e := AlgebraicGeometry.Scheme.OverField.Curve.ProjectiveLine.projectiveLineOverIsoNative K
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  refine ⟨f ≫ e.hom, ?_, ?_⟩
  · change IsFinite (f.left ≫ e.hom.left)
    infer_instance
  · change IsDominant (f.left ≫ e.hom.left)
    infer_instance

/-- The original curve-properties interface gives a finite map to actual native
P1, with no extra normality or dimension theorem-family parameter. -/
theorem curveProperties_exists_finite_dominant_map_to_nativeP1
    {X : FScheme K} (hX : Properties X) :
    ∃ f : X ⟶ Over.mk
      (_root_.AlgebraicGeometry.ProjectiveSpace.toSpec K (ULift.{u} (Fin 2))),
      IsFinite f.left ∧ IsDominant f.left := by
  obtain ⟨f, hf, hdom⟩ := curveProperties_exists_finite_dominant_map_to_projectiveP1 hX
  let : IsFinite f.left := hf
  let : IsDominant f.left := hdom
  let e := AlgebraicGeometry.Scheme.OverField.Curve.ProjectiveLine.projectiveLineOverIsoNative K
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  refine ⟨f ≫ e.hom, ?_, ?_⟩
  · change IsFinite (f.left ≫ e.hom.left)
    infer_instance
  · change IsDominant (f.left ≫ e.hom.left)
    infer_instance

end AlgebraicGeometry.Scheme.OverField.Curve.Projectivity
