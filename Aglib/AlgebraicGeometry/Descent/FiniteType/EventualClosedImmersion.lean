/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FiniteType.ChartLocality
public import Aglib.AlgebraicGeometry.Descent.FiniteType.EventualClosedChart

/-!
# Eventual closed immersion in a global base-change family

A finite affine cover of the original target gives finitely many eventual
closed chart arrows. Cofilteredness puts them at one common stage. The
actual cartesian transition squares preserve closedness there, and the
explicit chart-locality comparisons recover the original pulled arrow.
The original source and target are qcqs; base stages need not be affine.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

namespace BaseChangeChart

/-- Closedness on a chart persists along its actual cartesian transition maps. -/
lemma isClosedImmersion_stageMap_of_transition
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (i : I)
    {A B : Over (D.obj i)} (a : A ⟶ B) (V : B.left.Opens)
    {j k : Over i} (q : j ⟶ k) [IsClosedImmersion (stageMap D i a V k)] :
    IsClosedImmersion (stageMap D i a V j) :=
  @MorphismProperty.IsStableUnderBaseChange.of_isPullback
    Scheme.{u} _ (@IsClosedImmersion) IsClosedImmersion.isStableUnderBaseChange
    ((targetDiagram D i V).obj j) ((sourceDiagram D i a V).obj k)
    ((sourceDiagram D i a V).obj j) ((targetDiagram D i V).obj k)
    ((targetDiagram D i V).map q) (stageMap D i a V k)
    ((sourceDiagram D i a V).map q) (stageMap D i a V j)
    (isPullback_stageMap D i a V q).flip inferInstance

end BaseChangeChart

/-- Closedness of a finite-type arrow descends in an actual base-change family
with affine transition maps. Affine bases and finite presentation are not
assumed. The original source and target are required to be qcqs. -/
lemma exists_isClosedImmersion_baseChangeOverHom_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {A B : Over (D.obj i)} (a : A ⟶ B)
    [CompactSpace A.left] [QuasiSeparatedSpace A.left]
    [CompactSpace B.left] [QuasiSeparatedSpace B.left]
    [LocallyOfFiniteType a.left]
    [IsClosedImmersion (baseChangeOverHom (c.π.app i) a)] :
    ∃ j : Over i, IsClosedImmersion (baseChangeOverHom (D.map j.hom) a) := by
  classical
  let 𝒰 := B.left.affineCover.finiteSubcover
  let U (k : 𝒰.I₀) := (𝒰.f k).opensRange
  have (k : 𝒰.I₀) : IsAffine (U k).toScheme := isAffineOpen_opensRange (𝒰.f k)
  choose j hj using fun k : 𝒰.I₀ ↦
    BaseChangeChart.exists_isClosedImmersion_stageMap D i a (U k) c hc
  obtain ⟨l, hl⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
  let q (k : 𝒰.I₀) : l ⟶ j k :=
    (hl (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)).some
  have hclosed (k : 𝒰.I₀) :
      IsClosedImmersion (BaseChangeChart.baseChangeMap D i a (U k) (D.map l.hom)) := by
    have := hj k
    exact BaseChangeChart.isClosedImmersion_stageMap_of_transition D i a (U k) (q k)
  exact ⟨l, BaseChangeChart.isClosedImmersion_of_chart_cover D i a (D.map l.hom)
    U 𝒰.iSup_opensRange hclosed⟩

end AlgebraicGeometry.Scheme
