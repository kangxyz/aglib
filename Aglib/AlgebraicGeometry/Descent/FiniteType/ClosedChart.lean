/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FiniteType.ChartMaps

/-!
# Restricting an actual base-changed arrow to a target chart

The chart arrows are cartesian over the original base-changed arrow. The
comparison uses explicit pullback lifts and their projection identities,
not an identification of the underlying objects alone. Consequently a
closed original arrow gives a closed chart arrow, over any base change.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

namespace BaseChangeChart

variable {I : Type u} [Category.{u} I]
  (D : I ⥤ Scheme.{u}) (i : I)
  {A B : Over (D.obj i)} (a : A ⟶ B) (V : B.left.Opens)
  {T : Scheme.{u}} (b : T ⟶ D.obj i)

/-- The actual source-chart inclusion after base change. -/
def sourceInclusion : pullback b (source D i a V).hom ⟶ pullback b A.hom :=
  baseChangeOverHom b
    (Over.homMk (a.left ⁻¹ᵁ V).ι (by rfl) : source D i a V ⟶ A)

/-- The actual target-chart inclusion after base change. -/
def targetInclusion : pullback b (target D i V).hom ⟶ pullback b B.hom :=
  baseChangeOverHom b (Over.homMk V.ι (by rfl) : target D i V ⟶ B)

@[reassoc (attr := simp)]
lemma sourceInclusion_snd :
    sourceInclusion D i a V b ≫ pullback.snd b A.hom =
      pullback.snd b (source D i a V).hom ≫ (a.left ⁻¹ᵁ V).ι := by
  simp [sourceInclusion]

@[reassoc (attr := simp)]
lemma targetInclusion_snd :
    targetInclusion D i V b ≫ pullback.snd b B.hom =
      pullback.snd b (target D i V).hom ≫ V.ι := by
  simp [targetInclusion]

/-- The chart and original arrows commute with the specified inclusions. -/
@[reassoc]
lemma baseChangeMap_comp_targetInclusion :
    baseChangeMap D i a V b ≫ targetInclusion D i V b =
      sourceInclusion D i a V b ≫ baseChangeOverHom b a := by
  apply pullback.hom_ext <;>
    simp [sourceInclusion, targetInclusion, baseChangeOverHom, baseChangeMap, map]

/-- The actual chart arrow is the base change of the actual original arrow. -/
lemma isPullback_inclusions :
    IsPullback (baseChangeMap D i a V b) (sourceInclusion D i a V b)
      (targetInclusion D i V b) (baseChangeOverHom b a) := by
  apply IsPullback.of_bot (v₂₁ := pullback.snd b A.hom)
    (v₂₂ := pullback.snd b B.hom) _
    (baseChangeMap_comp_targetInclusion D i a V b) (isPullback_baseChangeOverHom b a)
  simpa only [sourceInclusion_snd, targetInclusion_snd] using
    (isPullback_baseChangeMap D i a V b).paste_vert
      (isPullback_morphismRestrict a.left V)

/-- Closedness of the original pulled arrow implies closedness on the chart. -/
lemma isClosedImmersion_baseChangeMap [IsClosedImmersion (baseChangeOverHom b a)] :
    IsClosedImmersion (baseChangeMap D i a V b) :=
  @MorphismProperty.IsStableUnderBaseChange.of_isPullback
    Scheme.{u} _ (@IsClosedImmersion) IsClosedImmersion.isStableUnderBaseChange
    (pullback b (target D i V).hom) (pullback b A.hom)
    (pullback b (source D i a V).hom) (pullback b B.hom)
    (targetInclusion D i V b) (baseChangeOverHom b a)
    (sourceInclusion D i a V b) (baseChangeMap D i a V b)
    (isPullback_inclusions D i a V b).flip inferInstance

end BaseChangeChart

end AlgebraicGeometry.Scheme
