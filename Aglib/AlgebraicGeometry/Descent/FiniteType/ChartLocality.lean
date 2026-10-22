/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FiniteType.ClosedChart

/-!
# Target locality for the specified chart arrows

The actual target-chart inclusion has range equal to the inverse image
of the original target open. Its cartesian square identifies the chart
arrow with the corresponding restriction of the original pulled arrow.
These comparisons let native target locality assemble chart closedness.
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
  {T : Scheme.{u}} (b : T ⟶ D.obj i)

/-- The actual target-chart inclusion is an open immersion. -/
instance targetInclusion_isOpenImmersion : IsOpenImmersion (targetInclusion D i V b) := by
  let v : target D i V ⟶ B := Over.homMk V.ι (by rfl)
  exact @MorphismProperty.IsStableUnderBaseChange.of_isPullback
    Scheme.{u} _ (@IsOpenImmersion) inferInstance
    (pullback b B.hom) V.toScheme (pullback b (target D i V).hom) B.left
    (pullback.snd b B.hom) V.ι (pullback.snd b (target D i V).hom)
    (targetInclusion D i V b) (isPullback_baseChangeOverHom b v).flip inferInstance

/-- The range of the actual chart inclusion is the prescribed inverse-image open. -/
lemma targetInclusion_opensRange :
    (targetInclusion D i V b).opensRange = pullback.snd b B.hom ⁻¹ᵁ V := by
  let v : target D i V ⟶ B := Over.homMk V.ι (by rfl)
  let H := isPullback_baseChangeOverHom b v
  have : IsOpenImmersion (baseChangeOverHom b v) :=
    inferInstanceAs (IsOpenImmersion (targetInclusion D i V b))
  have : IsOpenImmersion v.left := inferInstanceAs (IsOpenImmersion V.ι)
  have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H.flip ⊤
  simpa [v, targetInclusion] using h

/-- Closedness of the literal chart arrow implies closedness of the literal
restriction of the original arrow to the inverse-image target open. -/
lemma isClosedImmersion_restrict_baseChangeOverHom
    [IsClosedImmersion (baseChangeMap D i a V b)] :
    IsClosedImmersion (baseChangeOverHom b a ∣_ (pullback.snd b B.hom ⁻¹ᵁ V)) := by
  let H := (isPullback_inclusions D i a V b).flip
  have : IsClosedImmersion (pullback.snd (baseChangeOverHom b a) (targetInclusion D i V b)) := by
    rw [← H.isoPullback_inv_snd]
    infer_instance
  have h := (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (morphismRestrictOpensRange (baseChangeOverHom b a) (targetInclusion D i V b))).mpr
      (inferInstance : IsClosedImmersion
        (pullback.snd (baseChangeOverHom b a) (targetInclusion D i V b)))
  rwa [targetInclusion_opensRange D i V b] at h

/-- Closedness of an actual pulled arrow is local on any cover by fixed target opens. -/
lemma isClosedImmersion_of_chart_cover {κ : Type u} (U : κ → B.left.Opens)
    (hU : iSup U = ⊤)
    (hclosed : ∀ k, IsClosedImmersion (baseChangeMap D i a (U k) b)) :
    IsClosedImmersion (baseChangeOverHom b a) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
    (fun k ↦ pullback.snd b B.hom ⁻¹ᵁ U k)
  · rw [← Scheme.Hom.preimage_iSup, hU]
    simp
  · intro k
    have := hclosed k
    exact isClosedImmersion_restrict_baseChangeOverHom D i a (U k) b

end AlgebraicGeometry.Scheme.BaseChangeChart
