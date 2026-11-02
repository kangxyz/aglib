/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.SourceBaseChangeSquares
public import Aglib.AlgebraicGeometry.Compactification.Refinements.Densification

/-! # Actual normalization squares for source-isomorphism base change -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Hom.DenseCompactification

universe u
variable {X X' S T : Scheme.{u}} {f : X ⟶ S} (f' : X' ⟶ S)
  [QuasiCompact f] [QuasiCompact f'] (e : X' ≅ X) (he : e.hom ≫ f = f')
  (b : T ⟶ S) (C : Hom.DenseCompactification f)

omit [QuasiCompact f'] in
/-- The source-transported normalization has its original open immersion equation. -/
theorem sourceBCTransportNormalization_open :
    ((baseChange b ⋙ pullbackSourceTransport f' e he b).obj C).j ≫
        baseChangeNormalization b C =
      (sourceBaseChangeTransportModel f f' e he b C.toCompactification).j := by
  exact (Category.assoc _ _ _).trans (congrArg
    (fun z => (pullbackSourceIso f' e he b).hom ≫ z) (baseChange_j_normalization b C))

omit [QuasiCompact f'] in
/-- The original transported normalization is Cartesian on the unchanged open source. -/
theorem sourceBCTransportNormalization_isPullback :
    IsPullback ((baseChange b ⋙ pullbackSourceTransport f' e he b).obj C).j
      (𝟙 (pullback b f')) (baseChangeNormalization b C)
      (sourceBaseChangeTransportModel f f' e he b C.toCompactification).j := by
  let : Mono (show ((baseChange b ⋙ pullbackSourceTransport f' e he b).obj C).Xbar ⟶
      (sourceBaseChangeTransportModel f f' e he b C.toCompactification).Xbar from
        baseChangeNormalization b C) := inferInstanceAs (Mono (baseChangeNormalization b C))
  exact (IsPullback.of_horiz_isIso_mono
    (show CommSq (𝟙 (pullback b f'))
      ((baseChange b ⋙ pullbackSourceTransport f' e he b).obj C).j
      (sourceBaseChangeTransportModel f f' e he b C.toCompactification).j
      (baseChangeNormalization b C) from
      ⟨(Category.id_comp _).trans (sourceBCTransportNormalization_open f' e he b C).symm⟩)).flip

omit [QuasiCompact f] in
/-- The normalization of the source-first raw model is Cartesian over that same source. -/
theorem sourceBCActualNormalization_isPullback :
    IsPullback ((sourceIso f' e he ⋙ baseChange b).obj C).j
      (𝟙 (pullback b f')) (baseChangeNormalization b ((sourceIso f' e he).obj C))
      (((sourceIso f' e he).obj C).toCompactification.baseChange b).j :=
  Hom.Compactification.isPullback_densify
    (((sourceIso f' e he).obj C).toCompactification.baseChange b)

omit [QuasiCompact f] in
/-- The same actual normalization into the source-transported raw model. -/
theorem sourceBCFinalNormalization_open :
    ((sourceIso f' e he ⋙ baseChange b).obj C).j ≫
        baseChangeNormalization b ((sourceIso f' e he).obj C) =
      (sourceBaseChangeTransportModel f f' e he b C.toCompactification).j :=
  (baseChange_j_normalization b ((sourceIso f' e he).obj C)).trans
    (sourceBaseChange_open f f' e he b C.toCompactification)

omit [QuasiCompact f] in
/-- The final normalization into the actual transported raw ambient is Cartesian. -/
theorem sourceBCFinalNormalization_isPullback :
    IsPullback ((sourceIso f' e he ⋙ baseChange b).obj C).j
      (𝟙 (pullback b f')) (baseChangeNormalization b ((sourceIso f' e he).obj C))
      (sourceBaseChangeTransportModel f f' e he b C.toCompactification).j := by
  let : Mono (show ((sourceIso f' e he ⋙ baseChange b).obj C).Xbar ⟶
      (sourceBaseChangeTransportModel f f' e he b C.toCompactification).Xbar from
        baseChangeNormalization b ((sourceIso f' e he).obj C)) :=
    inferInstanceAs (Mono (baseChangeNormalization b ((sourceIso f' e he).obj C)))
  exact (IsPullback.of_horiz_isIso_mono
    (show CommSq (𝟙 (pullback b f')) ((sourceIso f' e he ⋙ baseChange b).obj C).j
      (sourceBaseChangeTransportModel f f' e he b C.toCompactification).j
      (baseChangeNormalization b ((sourceIso f' e he).obj C)) from
      ⟨(Category.id_comp _).trans (sourceBCFinalNormalization_open f' e he b C).symm⟩)).flip

end AlgebraicGeometry.Scheme.EtaleCohomology
