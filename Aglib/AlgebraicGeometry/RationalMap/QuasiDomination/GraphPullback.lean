/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.GraphBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Pulling back an actual closed partial graph

An arbitrary base map pulls a closed partial graph back to a closed partial
graph on the literal pullback of its domain. If that domain was open, the new
domain is open by base change. No flatness or schematic-density assertion is
made about the comparison map.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

variable {D B C Y S : Scheme.{u}}
variable (d : D ⟶ B) (h : D ⟶ Y) (pB : B ⟶ S) (pY : Y ⟶ S)
    (w : d ≫ pB = h ≫ pY) (b : C ⟶ B)

/-- The literal graph of the pulled-back partial map. -/
def baseChangeGraph : pullback d b ⟶ pullback (b ≫ pB) pY :=
  pullback.lift (pullback.snd d b) (pullback.fst d b ≫ h) (by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, w, Category.assoc])

@[reassoc (attr := simp)]
lemma baseChangeGraph_fst :
    baseChangeGraph d h pB pY w b ≫ pullback.fst (b ≫ pB) pY =
      pullback.snd d b :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma baseChangeGraph_snd :
    baseChangeGraph d h pB pY w b ≫ pullback.snd (b ≫ pB) pY =
      pullback.fst d b ≫ h :=
  pullback.lift_snd _ _ _

/-- The new graph is the actual base change of the original graph along the
canonical map of relative products. -/
lemma isPullback_baseChangeGraph :
    IsPullback (pullback.fst d b) (baseChangeGraph d h pB pY w b)
      (pullback.lift d h w) (productBaseChangeMap b pB pY) := by
  have hw : pullback.fst d b ≫ pullback.lift d h w =
      baseChangeGraph d h pB pY w b ≫ productBaseChangeMap b pB pY := by
    apply pullback.hom_ext
    · simp only [Category.assoc, productBaseChangeMap_fst, baseChangeGraph_fst_assoc]
      exact (congrArg (fun k ↦ pullback.fst d b ≫ k)
        (pullback.lift_fst d h w)).trans pullback.condition
    · simp only [Category.assoc, productBaseChangeMap_snd, baseChangeGraph_snd]
      exact congrArg (fun k ↦ pullback.fst d b ≫ k) (pullback.lift_snd d h w)
  apply IsPullback.of_isLimit (c := PullbackCone.mk (pullback.fst d b)
    (baseChangeGraph d h pB pY w b) hw)
  refine PullbackCone.IsLimit.mk _
    (fun s ↦ pullback.lift s.fst (s.snd ≫ pullback.fst (b ≫ pB) pY) (by
      have hs := congrArg (fun k ↦ k ≫ pullback.fst pB pY) s.condition
      simpa only [Category.assoc, pullback.lift_fst,
        productBaseChangeMap_fst] using hs)) ?_ ?_ ?_
  · intro s
    exact pullback.lift_fst _ _ _
  · intro s
    apply pullback.hom_ext
    · rw [Category.assoc, baseChangeGraph_fst]
      exact pullback.lift_snd _ _ _
    · have hs := congrArg (fun k ↦ k ≫ pullback.snd pB pY) s.condition
      simpa only [Category.assoc, baseChangeGraph_snd, pullback.lift_fst_assoc,
        pullback.lift_snd, productBaseChangeMap_snd] using hs
  · intro s m hm₁ hm₂
    apply pullback.hom_ext
    · simpa only [pullback.lift_fst] using hm₁
    · simpa only [Category.assoc, baseChangeGraph_fst, pullback.lift_snd] using
        congrArg (fun k ↦ k ≫ pullback.fst (b ≫ pB) pY) hm₂

/-- Closedness of the literal partial graph survives arbitrary base change. -/
instance baseChangeGraph_isClosedImmersion
    [IsClosedImmersion (pullback.lift d h w)] :
    IsClosedImmersion (baseChangeGraph d h pB pY w b) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeGraph d h pB pY w b) inferInstance

end AlgebraicGeometry.Scheme.QuasiDomination
