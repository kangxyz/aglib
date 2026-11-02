/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.CartesianBaseChange
public import Aglib.AlgebraicGeometry.Compactification.Refinements.BaseChangeIteration
public import Aglib.AlgebraicGeometry.Compactification.Refinements.RawRefinementBaseChange

/-! # Original raw pullback geometry for exceptional exchange coherence -/

@[expose] public noncomputable section
open CategoryTheory Limits
universe u

namespace AlgebraicGeometry.Scheme.Hom.DenseCompactification

variable {X S T U : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (b : T ⟶ S) (c : U ⟶ T) (C : DenseCompactification f)

/-- The single raw pullback on the actual iterated source, using the native
source-pullback associator rather than a relabelling of objects. -/
def iterationSingleRawModel : Compactification (pullback.fst c (pullback.fst b f)) :=
  (C.toCompactification.baseChange (c ≫ b)).ofSourceIso
    (pullback.fst c (pullback.fst b f)) (iteratedSourceIso (f := f) b c)
    (iteratedSourceIso_hom_fst b c)

/-- The transported original single normalization retains its original open
source equation. -/
theorem iterationSingleNormalization_open :
    ((baseChange (c ≫ b) ⋙ iteratedSourceTransport b c).obj C).j ≫
        baseChangeNormalization (c ≫ b) C = (iterationSingleRawModel b c C).j := by
  change ((iteratedSourceIso (f := f) b c).hom ≫ ((baseChange (c ≫ b)).obj C).j) ≫
      baseChangeNormalization (c ≫ b) C =
    (iteratedSourceIso (f := f) b c).hom ≫ (C.toCompactification.baseChange (c ≫ b)).j
  exact (Category.assoc _ _ _).trans
    (congrArg (fun z => (iteratedSourceIso (f := f) b c).hom ≫ z)
      (baseChange_j_normalization (c ≫ b) C))

/-- The transported single normalization square is the actual closed-inclusion
pullback above its original open source. -/
theorem isPullback_iterationSingleNormalization :
    IsPullback ((baseChange (c ≫ b) ⋙ iteratedSourceTransport b c).obj C).j
      (𝟙 (pullback c (pullback.fst b f))) (baseChangeNormalization (c ≫ b) C)
      (iterationSingleRawModel b c C).j := by
  let : Mono (show ((baseChange (c ≫ b) ⋙ iteratedSourceTransport b c).obj C).Xbar ⟶
      (iterationSingleRawModel b c C).Xbar from baseChangeNormalization (c ≫ b) C) :=
    inferInstanceAs (Mono (baseChangeNormalization (c ≫ b) C))
  exact (IsPullback.of_horiz_isIso_mono
    (show CommSq (𝟙 (pullback c (pullback.fst b f)))
      ((baseChange (c ≫ b) ⋙ iteratedSourceTransport b c).obj C).j
      (iterationSingleRawModel b c C).j (baseChangeNormalization (c ≫ b) C) from
      ⟨(Category.id_comp _).trans (iterationSingleNormalization_open b c C).symm⟩)).flip

/-- The actual iterated closed inclusion is likewise Cartesian above the
unchanged iterated open source. -/
theorem isPullback_iteratedNormalization :
    IsPullback ((baseChange b ⋙ baseChange c).obj C).j
      (𝟙 (pullback c (pullback.fst b f))) (iteratedNormalization b c C)
      (iterationSingleRawModel b c C).j := by
  let : Mono (show ((baseChange b ⋙ baseChange c).obj C).Xbar ⟶
      (iterationSingleRawModel b c C).Xbar from iteratedNormalization b c C) :=
    inferInstanceAs (Mono (iteratedNormalization b c C))
  exact (IsPullback.of_horiz_isIso_mono
    (show CommSq (𝟙 (pullback c (pullback.fst b f)))
      ((baseChange b ⋙ baseChange c).obj C).j
      (iterationSingleRawModel b c C).j (iteratedNormalization b c C) from
      ⟨(Category.id_comp _).trans
        ((iteratedNormalization_sourceTransport b c C).trans
          (iterationSingleNormalization_open b c C)).symm⟩)).flip

/-- The actual pullback of the first normalization is the original iterated
raw ambient map, with both projections unchanged. -/
theorem normalization_refinementBaseChangeMap :
    Compactification.refinementBaseChangeMap ((baseChange b).obj C).toCompactification
      (C.toCompactification.baseChange b) (baseChangeNormalization b C)
      (baseChangeNormalization_fst b C) c = iteratedRawMap b c C := by
  apply pullback.hom_ext
  · exact (Compactification.refinementBaseChangeMap_fst
      ((baseChange b).obj C).toCompactification (C.toCompactification.baseChange b)
      (baseChangeNormalization b C) (baseChangeNormalization_fst b C) c).trans
        (iteratedRawMap_fst b c C).symm
  · exact (Compactification.refinementBaseChangeMap_snd
      ((baseChange b).obj C).toCompactification (C.toCompactification.baseChange b)
      (baseChangeNormalization b C) (baseChangeNormalization_fst b C) c).trans
        (iteratedRawMap_snd b c C).symm

/-- The native ambient pullback associator, retaining the actual raw models. -/
def iterationRawAmbientIso :
    ((C.toCompactification.baseChange b).baseChange c).Xbar ≅
      (iterationSingleRawModel b c C).Xbar :=
  pullbackRightPullbackFstIso b C.p c

omit [QuasiCompact f] in
/-- The ambient associator preserves the actual proper structural map. -/
theorem iterationRawAmbientIso_hom_p :
    (iterationRawAmbientIso b c C).hom ≫ (iterationSingleRawModel b c C).p =
      ((C.toCompactification.baseChange b).baseChange c).p :=
  pullbackRightPullbackFstIso_hom_fst b C.p c

omit [QuasiCompact f] in
/-- The native source and ambient associators preserve the original raw open
immersion, proved through their actual pullback projections. -/
theorem iterationRawAmbientIso_open :
    ((C.toCompactification.baseChange b).baseChange c).j ≫
        (iterationRawAmbientIso b c C).hom = (iterationSingleRawModel b c C).j := by
  let j₁ : pullback b f ⟶ pullback b C.p := (C.toCompactification.baseChange b).j
  let j₂ : pullback c (pullback.fst b f) ⟶ pullback c (pullback.fst b C.p) :=
    ((C.toCompactification.baseChange b).baseChange c).j
  let j : pullback (c ≫ b) f ⟶ pullback (c ≫ b) C.p :=
    (C.toCompactification.baseChange (c ≫ b)).j
  let e := iteratedSourceIso (f := f) b c
  let q := pullbackRightPullbackFstIso b C.p c
  change j₂ ≫ q.hom = e.hom ≫ j
  apply pullback.hom_ext
  · calc
      (j₂ ≫ q.hom) ≫ pullback.fst (c ≫ b) C.p =
          j₂ ≫ (q.hom ≫ pullback.fst (c ≫ b) C.p) := Category.assoc _ _ _
      _ = j₂ ≫ pullback.fst c (pullback.fst b C.p) :=
        congrArg (fun z => j₂ ≫ z) (pullbackRightPullbackFstIso_hom_fst b C.p c)
      _ = pullback.fst c (pullback.fst b f) :=
        Compactification.baseChange_j_fst (C.toCompactification.baseChange b) c
      _ = e.hom ≫ pullback.fst (c ≫ b) f := (iteratedSourceIso_hom_fst b c).symm
      _ = (e.hom ≫ j) ≫ pullback.fst (c ≫ b) C.p :=
        ((Category.assoc _ _ _).trans (congrArg (fun z => e.hom ≫ z)
          (Compactification.baseChange_j_fst C.toCompactification (c ≫ b)))).symm
  · calc
      (j₂ ≫ q.hom) ≫ pullback.snd (c ≫ b) C.p =
          j₂ ≫ (q.hom ≫ pullback.snd (c ≫ b) C.p) := Category.assoc _ _ _
      _ = j₂ ≫ (pullback.snd c (pullback.fst b C.p) ≫ pullback.snd b C.p) :=
        congrArg (fun z => j₂ ≫ z) (pullbackRightPullbackFstIso_hom_snd b C.p c)
      _ = (pullback.snd c (pullback.fst b f) ≫ j₁) ≫ pullback.snd b C.p :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun z => z ≫ pullback.snd b C.p)
            (Compactification.baseChange_j_snd (C.toCompactification.baseChange b) c))
      _ = pullback.snd c (pullback.fst b f) ≫ (pullback.snd b f ≫ C.j) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun z => pullback.snd c (pullback.fst b f) ≫ z)
            (Compactification.baseChange_j_snd C.toCompactification b))
      _ = (e.hom ≫ pullback.snd (c ≫ b) f) ≫ C.j :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun z => z ≫ C.j) (iteratedSourceIso_hom_snd b c).symm)
      _ = (e.hom ≫ j) ≫ pullback.snd (c ≫ b) C.p :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun z => e.hom ≫ z)
            (Compactification.baseChange_j_snd C.toCompactification (c ≫ b)).symm).trans
              (Category.assoc _ _ _).symm)

omit [QuasiCompact f] in
/-- The actual ambient associator is Cartesian above the identical iterated
source; its original unit comparison is therefore available. -/
theorem isPullback_iterationRawAmbientIso :
    IsPullback ((C.toCompactification.baseChange b).baseChange c).j
      (𝟙 (pullback c (pullback.fst b f))) (iterationRawAmbientIso b c C).hom
      (iterationSingleRawModel b c C).j :=
  IsPullback.of_vert_isIso
    ⟨(iterationRawAmbientIso_open b c C).trans (Category.id_comp _).symm⟩

end AlgebraicGeometry.Scheme.Hom.DenseCompactification

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Hom.DenseCompactification

variable {X S T U : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (b : T ⟶ S) (c : U ⟶ T) (C : Hom.DenseCompactification f)

/-- The actual pulled-back normalization retains the Cartesian common-open square. -/
theorem isPullback_iterationPulledNormalization :
    IsPullback ((((baseChange b).obj C).toCompactification.baseChange c)).j (𝟙 (pullback c
      (pullback.fst b f)))
      (iteratedRawMap b c C) (((C.toCompactification.baseChange b).baseChange c)).j := by
  have hs := Hom.Compactification.isPullback_refinementBaseChangeMap_open
    ((baseChange b).obj C).toCompactification (C.toCompactification.baseChange b)
    (baseChangeNormalization b C) (baseChangeNormalization_fst b C) c
    (Hom.Compactification.isPullback_densify (C.toCompactification.baseChange b))
  exact (normalization_refinementBaseChangeMap b c C) ▸ hs

end AlgebraicGeometry.Scheme.EtaleCohomology
