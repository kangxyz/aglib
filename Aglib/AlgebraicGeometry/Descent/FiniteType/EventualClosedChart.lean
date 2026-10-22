/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FiniteType.AffineClosedImmersion
public import Aglib.AlgebraicGeometry.Descent.FiniteType.ClosedChart
public import Aglib.AlgebraicGeometry.Descent.FiniteType.EventualAffineChart

/-!
# Eventual closed immersion on one fixed target chart

Starting from closedness of the original limit arrow, restrict to a fixed
affine target chart, descend source affineness, and pass to the actual
`Over j` tail. The affine-system theorem then applies. Neither the original
base stages nor the original source stages are assumed affine. This is
one-chart descent; finite-cover synchronization and global target locality
remain separate steps.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.BaseChangeChart

variable {I : Type u} [Category.{u} I]
  (D : I ⥤ Scheme.{u}) (i : I)
  {A B : Over (D.obj i)} (a : A ⟶ B) (V : B.left.Opens)

/-- The local base-changed arrow retains local finite type of the original. -/
lemma locallyOfFiniteType_baseChangeMap [LocallyOfFiniteType a.left]
    {T : Scheme.{u}} (b : T ⟶ D.obj i) :
    LocallyOfFiniteType (baseChangeMap D i a V b) := by
  have : LocallyOfFiniteType (map D i a V).left :=
    inferInstanceAs (LocallyOfFiniteType (a.left ∣_ V))
  exact @MorphismProperty.IsStableUnderBaseChange.of_isPullback
    Scheme.{u} _ (@LocallyOfFiniteType) locallyOfFiniteType_isStableUnderBaseChange
    (pullback b (target D i V).hom) (source D i a V).left
    (pullback b (source D i a V).hom) (target D i V).left
    (pullback.snd b (target D i V).hom) (map D i a V).left
    (pullback.snd b (source D i a V).hom) (baseChangeMap D i a V b)
    (isPullback_baseChangeMap D i a V b).flip inferInstance

/-- Closedness descends on one fixed affine target chart. All affine stage
hypotheses used internally are derived on a later source-chart tail. -/
lemma exists_isClosedImmersion_stageMap [IsCofiltered I]
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [CompactSpace A.left] [QuasiSeparatedSpace A.left] [QuasiSeparatedSpace B.left]
    [LocallyOfFiniteType a.left] [IsAffine V.toScheme]
    (c : Cone D) (hc : IsLimit c)
    [IsClosedImmersion (baseChangeOverHom (c.π.app i) a)] :
    ∃ j : Over i, IsClosedImmersion (stageMap D i a V j) := by
  have : IsClosedImmersion (limitMap D i a V c) :=
    isClosedImmersion_baseChangeMap D i a V (c.π.app i)
  obtain ⟨j, hj⟩ := exists_isAffine_source_obj D i a V c hc
  let SD := sourceDiagram D i a V
  let ED := targetDiagram D i V
  have : IsAffine (SD.obj j) := hj
  let DS := Over.forget j ⋙ SD
  let ES := Over.forget j ⋙ ED
  let cS : Cone DS := (sourceCone D i a V c).whisker (Over.forget j)
  let cT : Cone ES := (targetCone D i V c).whisker (Over.forget j)
  have hS : IsLimit cS :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget j) (sourceCone D i a V c)).symm
      (isLimitSourceCone D i a V c hc)
  have hT : IsLimit cT :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget j) (targetCone D i V c)).symm
      (isLimitTargetCone D i V c hc)
  have (k : Over j) : IsAffine (DS.obj k) := by
    change IsAffine (SD.obj k.left)
    exact isAffine_of_isAffineHom (SD.map k.hom)
  have (k : Over j) : IsAffine (ES.obj k) :=
    inferInstanceAs (IsAffine ((targetDiagram D i V).obj k.left))
  let β : DS ⟶ ES := Functor.whiskerLeft (Over.forget j) (diagramMap D i a V)
  have hcompat (k : Over j) :
      limitMap D i a V c ≫ cT.π.app k = cS.π.app k ≫ β.app k :=
    limitMap_comp_π D i a V c k.left
  have : LocallyOfFiniteType (β.app (Over.mk (𝟙 j))) :=
    locallyOfFiniteType_baseChangeMap D i a V (D.map j.hom)
  have hcart (k : Over j) (q : k ⟶ Over.mk (𝟙 j)) :
      IsPullback (β.app k) (DS.map q) (ES.map q) (β.app (Over.mk (𝟙 j))) :=
    isPullback_stageMap D i a V q.left
  obtain ⟨k, _, hk⟩ := Scheme.exists_isClosedImmersion_app_of_isLimit_of_isAffine
    DS ES β cS hS cT hT (limitMap D i a V c) hcompat (Over.mk (𝟙 j)) hcart
  exact ⟨k.left, hk⟩

end AlgebraicGeometry.Scheme.BaseChangeChart
