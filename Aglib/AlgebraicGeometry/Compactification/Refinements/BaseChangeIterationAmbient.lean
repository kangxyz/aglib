/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.BaseChange
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# The original closed ambient map for iterated normalized base change

Base change the first closed normalization, then compose with the native
pullback-pasting isomorphism. The second normalization maps into the resulting
single raw ambient pullback by an actual closed immersion.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom.DenseCompactification

variable {X S T U : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (b : T ⟶ S) (c : U ⟶ T) (C : DenseCompactification f)

/-- Base change the first original normalization inclusion. -/
def iteratedRawMap : pullback c ((baseChange b).obj C).p ⟶
    pullback c (pullback.fst b C.p) :=
  pullback.map c ((baseChange b).obj C).p c (pullback.fst b C.p)
    (𝟙 U) (baseChangeNormalization b C) (𝟙 T)
    ((Category.comp_id c).trans (Category.id_comp c).symm)
    ((Category.comp_id _).trans (baseChangeNormalization_fst b C).symm)

instance iteratedRawMap_isClosedImmersion : IsClosedImmersion (iteratedRawMap b c C) := by
  unfold iteratedRawMap
  rw [pullback_map_eq_pullbackFstFstIso_inv]
  infer_instance

@[reassoc (attr := simp)]
lemma iteratedRawMap_fst :
    iteratedRawMap b c C ≫ pullback.fst c (pullback.fst b C.p) =
      pullback.fst c ((baseChange b).obj C).p :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
lemma iteratedRawMap_snd :
    iteratedRawMap b c C ≫ pullback.snd c (pullback.fst b C.p) =
      pullback.snd c ((baseChange b).obj C).p ≫ baseChangeNormalization b C :=
  pullback.lift_snd _ _ _

/-- The actual closed immersion from the iterated dense ambient to the single raw ambient. -/
def iteratedNormalization : ((baseChange b ⋙ baseChange c).obj C).Xbar ⟶
    pullback (c ≫ b) C.p :=
  baseChangeNormalization c ((baseChange b).obj C) ≫ iteratedRawMap b c C ≫
    (pullbackRightPullbackFstIso b C.p c).hom

instance iteratedNormalization_isClosedImmersion :
    IsClosedImmersion (iteratedNormalization b c C) :=
  inferInstanceAs (IsClosedImmersion
    (baseChangeNormalization c ((baseChange b).obj C) ≫ iteratedRawMap b c C ≫
      (pullbackRightPullbackFstIso b C.p c).hom))

/-- The iterated closed ambient map retains the original proper projection. -/
@[reassoc (attr := simp)]
lemma iteratedNormalization_fst :
    iteratedNormalization b c C ≫ pullback.fst (c ≫ b) C.p =
      ((baseChange b ⋙ baseChange c).obj C).p := by
  change (baseChangeNormalization c ((baseChange b).obj C) ≫ iteratedRawMap b c C ≫
      (pullbackRightPullbackFstIso b C.p c).hom) ≫ pullback.fst (c ≫ b) C.p = _
  simp only [Functor.comp_obj, Category.assoc, pullbackRightPullbackFstIso_hom_fst,
    iteratedRawMap_fst,
    baseChangeNormalization_fst]

/-- The other original projection is the composite of both normalization projections. -/
@[reassoc (attr := simp)]
lemma iteratedNormalization_snd :
    iteratedNormalization b c C ≫ pullback.snd (c ≫ b) C.p =
      baseChangeNormalization c ((baseChange b).obj C) ≫
        pullback.snd c ((baseChange b).obj C).p ≫
          baseChangeNormalization b C ≫ pullback.snd b C.p := by
  change (baseChangeNormalization c ((baseChange b).obj C) ≫ iteratedRawMap b c C ≫
      (pullbackRightPullbackFstIso b C.p c).hom) ≫ pullback.snd (c ≫ b) C.p = _
  simp only [Category.assoc, pullbackRightPullbackFstIso_hom_snd,
    iteratedRawMap_snd_assoc]

/-- Iteration uses the original native source-pullback associator. -/
def iteratedSourceIso : pullback c (pullback.fst b f) ≅ pullback (c ≫ b) f :=
  pullbackRightPullbackFstIso b f c

omit [QuasiCompact f] in
@[reassoc (attr := simp)]
lemma iteratedSourceIso_hom_fst :
    (iteratedSourceIso (f := f) b c).hom ≫ pullback.fst (c ≫ b) f =
      pullback.fst c (pullback.fst b f) :=
  pullbackRightPullbackFstIso_hom_fst b f c

omit [QuasiCompact f] in
@[reassoc (attr := simp)]
lemma iteratedSourceIso_hom_snd :
    (iteratedSourceIso (f := f) b c).hom ≫ pullback.snd (c ≫ b) f =
      pullback.snd c (pullback.fst b f) ≫ pullback.snd b f :=
  pullbackRightPullbackFstIso_hom_snd b f c

/-- The closed iterated ambient map preserves the original source after its native associator. -/
lemma iteratedNormalization_open :
    ((baseChange b ⋙ baseChange c).obj C).j ≫ iteratedNormalization b c C =
      (iteratedSourceIso (f := f) b c).hom ≫
        (C.toCompactification.baseChange (c ≫ b)).j := by
  apply pullback.hom_ext
  · rw [Category.assoc, iteratedNormalization_fst,
      ((baseChange b ⋙ baseChange c).obj C).fac]
    exact ((Category.assoc _ _ _).trans
      ((congrArg (fun k => (iteratedSourceIso (f := f) b c).hom ≫ k)
        (Compactification.baseChange_j_fst C.toCompactification (c ≫ b))).trans
          (iteratedSourceIso_hom_fst b c))).symm
  · rw [Category.assoc, iteratedNormalization_snd]
    calc
      _ = (pullback.snd c (pullback.fst b f) ≫ ((baseChange b).obj C).j) ≫
          baseChangeNormalization b C ≫ pullback.snd b C.p := by
        simpa only [Functor.comp_obj, Category.assoc] using
          congrArg (fun k => k ≫ baseChangeNormalization b C ≫ pullback.snd b C.p)
            (baseChange_j_normalization_snd c ((baseChange b).obj C))
      _ = pullback.snd c (pullback.fst b f) ≫ (pullback.snd b f ≫ C.j) := by
        simpa only [Category.assoc] using
          congrArg (fun k => pullback.snd c (pullback.fst b f) ≫ k)
            (baseChange_j_normalization_snd b C)
      _ = ((iteratedSourceIso (f := f) b c).hom ≫ pullback.snd (c ≫ b) f) ≫ C.j :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ C.j) (iteratedSourceIso_hom_snd b c).symm)
      _ = _ := (Category.assoc _ _ _).trans
        ((congrArg (fun k => (iteratedSourceIso (f := f) b c).hom ≫ k)
          (Compactification.baseChange_j_snd C.toCompactification (c ≫ b)).symm).trans
            (Category.assoc _ _ _).symm)

end AlgebraicGeometry.Scheme.Hom.DenseCompactification
