/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.SourceNormalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawSourceBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.NormalizedBaseChange

/-! # Original source/base-change normalization transition triangle -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients Hom.DenseCompactification

private theorem rawTransition_comp_of_eq
    {X S : Scheme} {f : X ⟶ S} (C D E : Hom.Compactification f)
    (h : C.Xbar ⟶ D.Xbar) (g : D.Xbar ⟶ E.Xbar) (k : C.Xbar ⟶ E.Xbar)
    (hk : h ≫ g = k)
    (sq : IsPullback C.j (𝟙 X) h D.j) (hp : h ≫ D.p = C.p)
    (sq' : IsPullback D.j (𝟙 X) g E.j) (hp' : g ≫ E.p = D.p)
    (sqk : IsPullback C.j (𝟙 X) k E.j) (hpk : k ≫ E.p = C.p)
    (Λ : Type _) [Ring Λ]
    [HasDerivedCategory (ModuleSheaf X Λ)] [HasDerivedCategory (ModuleSheaf S Λ)]
    [HasDerivedCategory (ModuleSheaf C.Xbar Λ)]
    [HasDerivedCategory (ModuleSheaf D.Xbar Λ)]
    [HasDerivedCategory (ModuleSheaf E.Xbar Λ)] :
    moduleRawCompactificationTransition D E g sq' hp' Λ ≫
        moduleRawCompactificationTransition C D h sq hp Λ =
      moduleRawCompactificationTransition C E k sqk hpk Λ := by
  subst k
  exact (moduleRawCompactificationTransition_comp C D h sq hp Λ E g sq' hp' sqk hpk).symm

universe u wL wT wR wN wN'
variable {X X' S T : Scheme.{u}} {f : X ⟶ S} (f' : X' ⟶ S)
  [QuasiCompact f] [QuasiCompact f'] (e : X' ≅ X) (he : e.hom ≫ f = f')
  (b : T ⟶ S) (C : Hom.DenseCompactification f) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wL} (ModuleSheaf (pullback b f') Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ)]
  [HasDerivedCategory.{wN} (ModuleSheaf ((baseChange b).obj C).Xbar Λ)]
  [HasDerivedCategory.{wN'} (ModuleSheaf ((sourceIso f' e he ⋙ baseChange b).obj C).Xbar Λ)]

local instance sourceBCNormRawModel : HasDerivedCategory.{wR}
    (ModuleSheaf (sourceBaseChangeTransportModel f f' e he b C.toCompactification).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ))
local instance sourceBCNormActualRawModel : HasDerivedCategory.{wR}
    (ModuleSheaf (((sourceIso f' e he).obj C).toCompactification.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ))
local instance sourceBCNormTransportDenseModel : HasDerivedCategory.{wN}
    (ModuleSheaf ((baseChange b ⋙ pullbackSourceTransport f' e he b).obj C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN} (ModuleSheaf ((baseChange b).obj C).Xbar Λ))
local instance sourceBCNormActualDenseModel : HasDerivedCategory.{wN'}
    (ModuleSheaf (Hom.Compactification.densify
      (((sourceIso f' e he).obj C).toCompactification.baseChange b)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN'}
    (ModuleSheaf ((sourceIso f' e he ⋙ baseChange b).obj C).Xbar Λ))

/-- Original transported normalization, with its unchanged derived middle model. -/
def moduleSourceBCTransportNormalizationMap :=
  moduleRawCompactificationTransition
    ((baseChange b ⋙ pullbackSourceTransport f' e he b).obj C).toCompactification
    (sourceBaseChangeTransportModel f f' e he b C.toCompactification)
    (baseChangeNormalization b C) (sourceBCTransportNormalization_isPullback f' e he b C)
    (baseChangeNormalization_fst b C) Λ

/-- Original refinement induced by the actual normalized source/base-change isomorphism. -/
def moduleSourceBCNormalizedTransition :=
  moduleRawCompactificationTransition
    ((sourceIso f' e he ⋙ baseChange b).obj C).toCompactification
    ((baseChange b ⋙ pullbackSourceTransport f' e he b).obj C).toCompactification
    (baseChangeSourceIsoComponent f' e he b C).hom.hom
    (isPullback_open (baseChangeSourceIsoComponent f' e he b C).hom)
    (baseChangeSourceIsoComponent f' e he b C).hom.base_fac Λ

/-- The common original direct normalization route into the transported raw ambient. -/
def moduleSourceBCFinalNormalizationMap :=
  moduleRawCompactificationTransition
    ((sourceIso f' e he ⋙ baseChange b).obj C).toCompactification
    (sourceBaseChangeTransportModel f f' e he b C.toCompactification)
    (baseChangeNormalization b ((sourceIso f' e he).obj C))
    (sourceBCFinalNormalization_isPullback f' e he b C)
    (baseChangeNormalization_fst b ((sourceIso f' e he).obj C)) Λ

/-- Composition through the actual normalized comparison equals the original final route. -/
theorem moduleSourceBCNormalization_dense_triangle :
    moduleSourceBCTransportNormalizationMap f' e he b C Λ ≫
      moduleSourceBCNormalizedTransition f' e he b C Λ =
        moduleSourceBCFinalNormalizationMap f' e he b C Λ := by
  let A := (sourceIso f' e he ⋙ baseChange b).obj C
  let B := (baseChange b ⋙ pullbackSourceTransport f' e he b).obj C
  let R := sourceBaseChangeTransportModel f f' e he b C.toCompactification
  let r := (baseChangeSourceIsoComponent f' e he b C).hom
  exact rawTransition_comp_of_eq A.toCompactification B.toCompactification R
    r.hom (baseChangeNormalization b C)
    (baseChangeNormalization b ((sourceIso f' e he).obj C))
    (baseChangeSourceIsoComponent_normalization f' e he b C)
    (isPullback_open r) r.base_fac
    (sourceBCTransportNormalization_isPullback f' e he b C)
    (baseChangeNormalization_fst b C)
    (sourceBCFinalNormalization_isPullback f' e he b C)
    (baseChangeNormalization_fst b ((sourceIso f' e he).obj C)) Λ

omit [QuasiCompact f]
  [HasDerivedCategory.{wN} (ModuleSheaf ((baseChange b).obj C).Xbar Λ)] in
/-- Composition through the original raw identity-ambient comparison equals that same route. -/
theorem moduleSourceBCNormalization_raw_triangle :
    moduleRawSourceBaseChangeTransition f f' e he b C.toCompactification Λ ≫
      moduleCompactificationDensificationMap
        (((sourceIso f' e he).obj C).toCompactification.baseChange b) Λ =
      moduleSourceBCFinalNormalizationMap f' e he b C Λ := by
  let A := (sourceIso f' e he ⋙ baseChange b).obj C
  let B := ((sourceIso f' e he).obj C).toCompactification.baseChange b
  let R := sourceBaseChangeTransportModel f f' e he b C.toCompactification
  let n := baseChangeNormalization b ((sourceIso f' e he).obj C)
  exact rawTransition_comp_of_eq A.toCompactification B R n (𝟙 (pullback b C.p)) n
    (Category.comp_id n) (sourceBCActualNormalization_isPullback f' e he b C)
    (baseChangeNormalization_fst b ((sourceIso f' e he).obj C))
    (sourceBaseChange_open_isPullback f f' e he b C.toCompactification)
    (Category.id_comp (pullback.fst b C.p))
    (sourceBCFinalNormalization_isPullback f' e he b C)
    (baseChangeNormalization_fst b ((sourceIso f' e he).obj C)) Λ

end AlgebraicGeometry.Scheme.EtaleCohomology
