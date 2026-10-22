/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FiniteType.ChartMaps

/-!
# Eventual affineness of a source chart

A closed limit arrow into a fixed affine target chart has affine source.
The actual source-chart system is qcqs with affine transition maps, so
native eventual-affineness descent applies. The closed-immersion premise
here concerns the specified local limit arrow; deriving it from a global
limit arrow is a separate restriction/base-change comparison.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.BaseChangeChart

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (i : I)
  [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
  {A B : Over (D.obj i)} (a : A ⟶ B) (V : B.left.Opens)
  [IsAffine V.toScheme] (c : Cone D) (hc : IsLimit c)

include hc

/-- The canonical target-chart limit is affine, without affine base stages. -/
lemma isAffine_targetCone : IsAffine (targetCone D i V c).pt := by
  have : IsAffineHom ((targetCone D i V c).π.app (Over.mk (𝟙 i))) :=
    isAffineHom_π_app (targetDiagram D i V) (targetCone D i V c)
      (isLimitTargetCone D i V c hc) (Over.mk (𝟙 i))
  exact isAffine_of_isAffineHom ((targetCone D i V c).π.app (Over.mk (𝟙 i)))

/-- A closed local limit arrow over an affine target chart has affine source. -/
lemma isAffine_sourceCone [IsClosedImmersion (limitMap D i a V c)] :
    IsAffine (sourceCone D i a V c).pt := by
  have := isAffine_targetCone D i V c hc
  exact isAffine_of_isAffineHom (limitMap D i a V c)

/-- Affineness of the source of a closed local limit arrow descends to an
actual stage of the original `Over i` source-chart system. -/
lemma exists_isAffine_source_obj
    [CompactSpace A.left] [QuasiSeparatedSpace A.left] [QuasiSeparatedSpace B.left]
    [IsClosedImmersion (limitMap D i a V c)] :
    ∃ j : Over i, IsAffine ((sourceDiagram D i a V).obj j) := by
  have (j : Over i) : CompactSpace ((sourceDiagram D i a V).obj j) :=
    compactSpace_source_obj D i a V j
  have (j : Over i) : QuasiSeparatedSpace ((sourceDiagram D i a V).obj j) :=
    quasiSeparatedSpace_source_obj D i a V j
  have := isAffine_sourceCone D i a V c hc
  exact Scheme.exists_isAffine_of_isLimit (sourceDiagram D i a V)
    (sourceCone D i a V c) (isLimitSourceCone D i a V c hc)

end AlgebraicGeometry.Scheme.BaseChangeChart
