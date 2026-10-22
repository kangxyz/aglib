/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Immersions from literal product charts

The restricted pair maps and the product-chart open immersions are actual
pullback lifts and maps. Their triangles and inverse-image identities imply a
global immersion by native target-locality near the image of the source.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable {X Y S T : Scheme.{u}}

/-- The actual open chart in a fibre product obtained from two factor opens. -/
def pullbackOpenMap (a : Y ⟶ T) (b : S ⟶ T) (W : Y.Opens) (U : S.Opens) :
    pullback (W.ι ≫ a) (U.ι ≫ b) ⟶ pullback a b :=
  pullback.map _ _ _ _ W.ι U.ι (𝟙 T) (by simp) (by simp)

instance (a : Y ⟶ T) (b : S ⟶ T) (W : Y.Opens) (U : S.Opens) :
    IsOpenImmersion (pullbackOpenMap a b W U) := by
  dsimp [pullbackOpenMap]
  infer_instance

/-- The product-chart range is the intersection of the two literal inverse images. -/
lemma pullbackOpenMap_opensRange (a : Y ⟶ T) (b : S ⟶ T)
    (W : Y.Opens) (U : S.Opens) :
    (pullbackOpenMap a b W U).opensRange =
      pullback.fst a b ⁻¹ᵁ W ⊓ pullback.snd a b ⁻¹ᵁ U := by
  apply Opens.ext
  simp [pullbackOpenMap, Pullback.range_map]

/-- The literal restricted pair into a product chart. -/
def pullbackLiftResLE (a : Y ⟶ T) (b : S ⟶ T) (p : X ⟶ Y) (q : X ⟶ S)
    (hpq : p ≫ a = q ≫ b) (V : X.Opens) (W : Y.Opens) (U : S.Opens)
    (hVW : V ≤ p ⁻¹ᵁ W) (hVU : V ≤ q ⁻¹ᵁ U) :
    V.toScheme ⟶ pullback (W.ι ≫ a) (U.ι ≫ b) :=
  pullback.lift (f := W.ι ≫ a) (g := U.ι ≫ b)
    (p.resLE W V hVW) (q.resLE U V hVU) (by
      calc
        p.resLE W V hVW ≫ (W.ι ≫ a) = V.ι ≫ (p ≫ a) := by
          rw [Hom.resLE_comp_ι_assoc]
        _ = V.ι ≫ (q ≫ b) := congrArg (V.ι ≫ ·) hpq
        _ = q.resLE U V hVU ≫ (U.ι ≫ b) := by
          rw [Hom.resLE_comp_ι_assoc])

/-- The local pair retains the actual global pair and original source inclusion. -/
@[reassoc]
lemma pullbackLiftResLE_comp (a : Y ⟶ T) (b : S ⟶ T) (p : X ⟶ Y) (q : X ⟶ S)
    (hpq : p ≫ a = q ≫ b) (V : X.Opens) (W : Y.Opens) (U : S.Opens)
    (hVW : V ≤ p ⁻¹ᵁ W) (hVU : V ≤ q ⁻¹ᵁ U) :
    pullbackLiftResLE a b p q hpq V W U hVW hVU ≫ pullbackOpenMap a b W U =
      V.ι ≫ pullback.lift p q hpq := by
  apply pullback.hom_ext <;> simp [pullbackLiftResLE, pullbackOpenMap, Category.assoc]

/-- The source chart is exactly the inverse image of the product-chart range. -/
lemma preimage_pullbackOpenMap_opensRange
    (a : Y ⟶ T) (b : S ⟶ T) (p : X ⟶ Y) (q : X ⟶ S)
    (hpq : p ≫ a = q ≫ b) (V : X.Opens) (W : Y.Opens) (U : S.Opens)
    (hVW : V = p ⁻¹ᵁ W) (hVU : V ≤ q ⁻¹ᵁ U) :
    pullback.lift p q hpq ⁻¹ᵁ (pullbackOpenMap a b W U).opensRange = V := by
  rw [pullbackOpenMap_opensRange, Hom.preimage_inf, ← Hom.comp_preimage,
    ← Hom.comp_preimage, pullback.lift_fst, pullback.lift_snd, ← hVW]
  exact inf_eq_left.mpr hVU

/-- A source cover by exact product-chart inverse images detects immersion of
its literal pair map. The charts need only cover the image, not the product. -/
lemma isImmersion_pullback_lift_of_cover
    (a : Y ⟶ T) (b : S ⟶ T) (p : X ⟶ Y) (q : X ⟶ S)
    (hpq : p ≫ a = q ≫ b) {J : Type v}
    (V : J → X.Opens) (W : J → Y.Opens) (U : J → S.Opens)
    (hcover : IsOpenCover V) (hVW : ∀ j, V j = p ⁻¹ᵁ W j)
    (hVU : ∀ j, V j ≤ q ⁻¹ᵁ U j)
    (hlocal : ∀ j, IsImmersion
      (pullbackLiftResLE a b p q hpq (V j) (W j) (U j) (hVW j).le (hVU j))) :
    IsImmersion (pullback.lift p q hpq) := by
  let : MorphismProperty.RespectsRight (@IsImmersion) (@IsOpenImmersion) :=
    { postcomp := fun i hi g hg => by
        let : IsOpenImmersion i := hi
        let : IsImmersion g := hg
        infer_instance }
  let : MorphismProperty.HasOfPostcompProperty (@IsImmersion) (@IsOpenImmersion) :=
    { of_postcomp := fun g k _ hgk => by
        let : IsImmersion (g ≫ k) := hgk
        exact IsImmersion.of_comp g k }
  apply IsZariskiLocalAtTarget.of_forall_source_exists_preimage (P := @IsImmersion)
  intro x
  obtain ⟨j, hx⟩ := hcover.exists_mem x
  have he := preimage_pullbackOpenMap_opensRange a b p q hpq
    (V j) (W j) (U j) (hVW j) (hVU j)
  refine ⟨(pullbackOpenMap a b (W j) (U j)).opensRange, ?_, ?_⟩
  · change x ∈ pullback.lift p q hpq ⁻¹ᵁ
      (pullbackOpenMap a b (W j) (U j)).opensRange
    rwa [he]
  · rw [he, ← pullbackLiftResLE_comp a b p q hpq (V j) (W j) (U j)
      (hVW j).le (hVU j)]
    let := hlocal j
    infer_instance

end AlgebraicGeometry.Scheme
