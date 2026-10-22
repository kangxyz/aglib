/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.Range
public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.Dominance
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Restricting a graph to a target open and its source image

The graph on the inverse image of a target open factors through the actual
schematic image of its source map. Its square with the original graph is
cartesian, using the target-open pullback and the monicity of the image
inclusion. Consequently closedness over a protected source open passes to
this actual image model. No schematic-image base-change identity, reducedness,
properness, or density of the original source is asserted or assumed.

For a quasi-compact immersion, the map to this image is already an open
immersion and dominant in Mathlib; `isSchemeTheoreticallyDominant_toImage`
supplies its schematic dominance without reducedness.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

variable {U X Y S : Scheme.{u}} (j : U ⟶ X) (g : U ⟶ Y) (O : Y.Opens)
    (p : X ⟶ S) (f : Y ⟶ S) (w : j ≫ p = g ≫ f)

/-- The original source map restricted to the inverse image of the target open. -/
def targetOpenSourceMap : (g ⁻¹ᵁ O).toScheme ⟶ X := (g ⁻¹ᵁ O).ι ≫ j

/-- The literal graph on the actual source-image model and the target open. -/
def targetOpenImageGraph : (g ⁻¹ᵁ O).toScheme ⟶
    pullback ((targetOpenSourceMap j g O).imageι ≫ p) (O.ι ≫ f) :=
  pullback.lift (targetOpenSourceMap j g O).toImage (g ∣_ O) (by
    rw [← Category.assoc, Hom.toImage_imageι]
    simp only [targetOpenSourceMap, Category.assoc, w, ← morphismRestrict_ι_assoc])

@[reassoc (attr := simp)]
lemma targetOpenImageGraph_fst :
    targetOpenImageGraph j g O p f w ≫
      pullback.fst ((targetOpenSourceMap j g O).imageι ≫ p) (O.ι ≫ f) =
      (targetOpenSourceMap j g O).toImage := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma targetOpenImageGraph_snd :
    targetOpenImageGraph j g O p f w ≫
      pullback.snd ((targetOpenSourceMap j g O).imageι ≫ p) (O.ι ≫ f) =
      g ∣_ O := pullback.lift_snd _ _ _

/-- The canonical product map from the image model and target open. -/
def targetOpenImageProductMap :
    pullback ((targetOpenSourceMap j g O).imageι ≫ p) (O.ι ≫ f) ⟶ pullback p f :=
  pullback.map _ _ p f (targetOpenSourceMap j g O).imageι O.ι (𝟙 S)
    (by simp) (by simp)

@[reassoc (attr := simp)]
lemma targetOpenImageProductMap_fst :
    targetOpenImageProductMap j g O p f ≫ pullback.fst p f =
      pullback.fst ((targetOpenSourceMap j g O).imageι ≫ p) (O.ι ≫ f) ≫
        (targetOpenSourceMap j g O).imageι := by
  simp [targetOpenImageProductMap]

@[reassoc (attr := simp)]
lemma targetOpenImageProductMap_snd :
    targetOpenImageProductMap j g O p f ≫ pullback.snd p f =
      pullback.snd ((targetOpenSourceMap j g O).imageι ≫ p) (O.ι ≫ f) ≫ O.ι := by
  simp [targetOpenImageProductMap]

/-- This is a pullback of the original graph, not a base-change assertion for
schematic images. The original target-open square supplies the lift. -/
lemma isPullback_targetOpenImageGraph :
    IsPullback (targetOpenImageGraph j g O p f w) (g ⁻¹ᵁ O).ι
      (targetOpenImageProductMap j g O p f) (pullback.lift j g w) := by
  have hw : targetOpenImageGraph j g O p f w ≫ targetOpenImageProductMap j g O p f =
      (g ⁻¹ᵁ O).ι ≫ pullback.lift j g w := by
    apply pullback.hom_ext <;>
      simp [targetOpenImageProductMap, targetOpenImageGraph, targetOpenSourceMap]
  apply IsPullback.of_isLimit (c := PullbackCone.mk
    (targetOpenImageGraph j g O p f w) (g ⁻¹ᵁ O).ι hw)
  let H := isPullback_morphismRestrict g O
  refine PullbackCone.IsLimit.mk _
    (fun s => H.lift
      (s.fst ≫ pullback.snd ((targetOpenSourceMap j g O).imageι ≫ p) (O.ι ≫ f))
      s.snd (by
        have h := congrArg (fun k => k ≫ pullback.snd p f) s.condition
        simpa only [Category.assoc, targetOpenImageProductMap_snd,
          pullback.lift_snd] using h)) ?_ ?_ ?_
  · intro s
    apply pullback.hom_ext
    · apply (cancel_mono (targetOpenSourceMap j g O).imageι).mp
      have h := congrArg (fun k => k ≫ pullback.fst p f) s.condition
      simp only [Category.assoc, targetOpenImageGraph_fst_assoc, Hom.toImage_imageι]
      change H.lift _ _ _ ≫ (g ⁻¹ᵁ O).ι ≫ j = _
      rw [H.lift_snd_assoc]
      simpa only [Category.assoc, targetOpenImageProductMap_fst,
        pullback.lift_fst] using h.symm
    · simp
  · intro s
    simp
  · intro s m hm₁ hm₂
    apply (cancel_mono (g ⁻¹ᵁ O).ι).mp
    simpa [H] using hm₂

/-- Exact underlying graph range in the image/target-open product. -/
lemma range_targetOpenImageGraph :
    Set.range (targetOpenImageGraph j g O p f w) =
      targetOpenImageProductMap j g O p f ⁻¹' Set.range (pullback.lift j g w) :=
  Scheme.Pullback.Transport.range_eq_preimage_of_isPullback
    (isPullback_targetOpenImageGraph j g O p f w)

/-- Closedness of the original graph over `V` passes to its actual source
image over `imageι ⁻¹ᵁ V`, with the original target-open map unchanged. -/
lemma isClosed_targetOpenImageGraph_over (V : X.Opens)
    (hclosed : IsClosed ((pullback.fst p f ⁻¹ᵁ V).ι ⁻¹'
      Set.range (pullback.lift j g w))) :
    IsClosed ((pullback.fst ((targetOpenSourceMap j g O).imageι ≫ p) (O.ι ≫ f) ⁻¹ᵁ
      ((targetOpenSourceMap j g O).imageι ⁻¹ᵁ V)).ι ⁻¹'
        Set.range (targetOpenImageGraph j g O p f w)) := by
  let A := pullback.fst p f ⁻¹ᵁ V
  let B := pullback.fst ((targetOpenSourceMap j g O).imageι ≫ p) (O.ι ≫ f) ⁻¹ᵁ
    ((targetOpenSourceMap j g O).imageι ⁻¹ᵁ V)
  let k := targetOpenImageProductMap j g O p f
  let kV : B.toScheme → A.toScheme := fun x => ⟨k x.1, by
    change (k ≫ pullback.fst p f) x.1 ∈ V
    rw [targetOpenImageProductMap_fst]
    exact x.property⟩
  have hkV : Continuous kV :=
    (k.continuous.comp continuous_subtype_val).subtype_mk _
  have heq : B.ι ⁻¹' Set.range (targetOpenImageGraph j g O p f w) =
      kV ⁻¹' (A.ι ⁻¹' Set.range (pullback.lift j g w)) := by
    rw [range_targetOpenImageGraph]
    rfl
  change IsClosed (B.ι ⁻¹' Set.range (targetOpenImageGraph j g O p f w))
  rw [heq]
  exact hclosed.preimage hkV

end AlgebraicGeometry.Scheme.QuasiDomination
