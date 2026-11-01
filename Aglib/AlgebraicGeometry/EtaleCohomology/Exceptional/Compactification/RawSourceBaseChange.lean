/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.SourceBaseChangeSquares
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawSourceIsoBefore
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawTargetIso
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawSquareCongruence
public import Aglib.CategoryTheory.NatTrans.RefinedSourcePasting

/-! # Original raw base change and actual source-isomorphism interchange -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wX' wL wL' wS wT wM wN
variable {X X' S T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S)
  (e : X' ≅ X) (he : e.hom ≫ f = f') (b : T ⟶ S) (C : Hom.Compactification f)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wL} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wL'} (ModuleSheaf (pullback b f') Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wN} (ModuleSheaf (pullback b C.p) Λ)]

local instance rawSourceBCSourceModel : HasDerivedCategory.{wM}
    (ModuleSheaf (C.ofSourceIso f' e he).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))
local instance rawSourceBCPullbackModel : HasDerivedCategory.{wN}
    (ModuleSheaf (C.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN} (ModuleSheaf (pullback b C.p) Λ))
local instance rawSourceBCPullbackSourceModel : HasDerivedCategory.{wN}
    (ModuleSheaf (pullback b (C.ofSourceIso f' e he).p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN} (ModuleSheaf (pullback b C.p) Λ))
local instance rawSourceBCActualModel : HasDerivedCategory.{wN}
    (ModuleSheaf ((C.ofSourceIso f' e he).baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN} (ModuleSheaf (pullback b C.p) Λ))
local instance rawSourceBCTransportModel : HasDerivedCategory.{wN}
    (ModuleSheaf (sourceBaseChangeTransportModel f f' e he b C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN} (ModuleSheaf (pullback b C.p) Λ))

/-- Original composite-source exchange on the actual source-transported raw base change. -/
def moduleRawSourceBaseChangeCompositeMap :=
  moduleRawSquareMap C ((C.ofSourceIso f' e he).baseChange b)
    (pullback.snd b f' ≫ e.hom) (pullback.snd b C.p) b
    (sourceBaseChange_totalOpen f f' e he b C) (IsPullback.of_hasPullback b C.p).flip Λ

/-- Original identity-ambient transition between the two actual raw models. -/
def moduleRawSourceBaseChangeTransition :=
  moduleRawCompactificationTransition ((C.ofSourceIso f' e he).baseChange b)
    (sourceBaseChangeTransportModel f f' e he b C) (𝟙 (pullback b C.p))
    (sourceBaseChange_open_isPullback f f' e he b C)
    (Category.id_comp (pullback.fst b C.p)) Λ

/-- The actual universal source equality followed by the original torsion compositor. -/
def moduleRawSourceBaseChangeSourceIso :
    moduleDerivedInverseImageTorsion (pullback.snd b f' ≫ e.hom) Λ ≅
      moduleDerivedInverseImageTorsion (pullback.snd b f) Λ ⋙
        moduleDerivedInverseImageTorsion (sourceBaseChangeIso f f' e he b).hom Λ :=
  eqToIso (congrArg (fun a => moduleDerivedInverseImageTorsion a Λ)
      (sourceBaseChangeIso_hom_snd f f' e he b).symm) ≪≫
    moduleDerivedInverseImageTorsionCompIso Λ (pullback.snd b f)
      (sourceBaseChangeIso f f' e he b).hom

omit [HasDerivedCategory.{wL} (ModuleSheaf (pullback b f) Λ)] in
/-- Source transport first, then raw base change: the literal original composite exchange. -/
theorem moduleRawSourceBaseChange_before :
    SourceIsoBeforeExchangeEquation (moduleRawCompactificationSourceIso e Λ f' he C)
      (moduleRawCompactificationBaseChangeIso (C.ofSourceIso f' e he) b Λ).hom
      (moduleRawSourceBaseChangeCompositeMap f f' e he b C Λ)
      (moduleDerivedInverseImageTorsionCompIso Λ e.hom (pullback.snd b f')) :=
  moduleRawSquareMap_sourceIso_before C e f' he ((C.ofSourceIso f' e he).baseChange b)
    (pullback.snd b f') (pullback.snd b C.p) b
    (isPullback_rawCompactificationOpen (C.ofSourceIso f' e he) b)
    (sourceBaseChange_totalOpen f f' e he b C) (IsPullback.of_hasPullback b C.p).flip Λ

omit [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)] in
/-- Base change first, then actual source transport and original ambient refinement:
this is the same literal original composite exchange. -/
theorem moduleRawSourceBaseChange_after :
    RefinedSourceIsoPastingEquation (moduleRawCompactificationBaseChangeIso C b Λ).hom
      (moduleRawSourceBaseChangeCompositeMap f f' e he b C Λ)
      (moduleRawSourceBaseChangeSourceIso f f' e he b Λ)
      (moduleRawCompactificationSourceIso (sourceBaseChangeIso f f' e he b) Λ
        (pullback.fst b f') (sourceBaseChangeIso_hom_fst f f' e he b) (C.baseChange b))
      (moduleRawSourceBaseChangeTransition f f' e he b C Λ) := by
  let a := pullback.snd b f' ≫ e.hom
  let a' := (sourceBaseChangeIso f f' e he b).hom ≫ pullback.snd b f
  let D := C.baseChange b
  let E := sourceBaseChangeTransportModel f f' e he b C
  let I := (C.ofSourceIso f' e he).baseChange b
  let q := pullback.snd b C.p
  let hp := (IsPullback.of_hasPullback b C.p).flip
  let : IsIso (show I.Xbar ⟶ E.Xbar from 𝟙 (pullback b C.p)) :=
    inferInstanceAs (IsIso (𝟙 (pullback b C.p)))
  exact refinedSourceIsoPasting_of_equations
    (moduleRawSquareMap C D (pullback.snd b f) q b
      (isPullback_rawCompactificationOpen C b) hp Λ)
    (moduleRawSquareMap C E a' q b (sourceBaseChange_transportOpen f f' e he b C) hp Λ)
    (moduleRawSquareMap C E a q b (sourceBaseChange_transportTotalOpen f f' e he b C) hp Λ)
    (moduleRawSourceBaseChangeCompositeMap f f' e he b C Λ)
    (eqToIso (congrArg (fun z => moduleDerivedInverseImageTorsion z Λ)
      (sourceBaseChangeIso_hom_snd f f' e he b).symm))
    (moduleDerivedInverseImageTorsionCompIso Λ (pullback.snd b f)
      (sourceBaseChangeIso f f' e he b).hom)
    (moduleRawCompactificationSourceIso (sourceBaseChangeIso f f' e he b) Λ
      (pullback.fst b f') (sourceBaseChangeIso_hom_fst f f' e he b) D)
    (moduleRawSourceBaseChangeTransition f f' e he b C Λ)
    (moduleRawSquareMap_targetIso C I E a q q b (𝟙 (pullback b C.p))
      (sourceBaseChange_open_isPullback f f' e he b C)
      (Category.id_comp (pullback.fst b C.p)) (Category.id_comp q)
      (sourceBaseChange_totalOpen f f' e he b C)
      (sourceBaseChange_transportTotalOpen f f' e he b C) hp hp Λ)
    (moduleRawSquareMap_congr_source C E a a'
      (sourceBaseChangeIso_hom_snd f f' e he b).symm q b
      (sourceBaseChange_transportTotalOpen f f' e he b C)
      (sourceBaseChange_transportOpen f f' e he b C) hp Λ)
    (moduleRawSquareMap_sourceIso_pasting C D (pullback.snd b f) q b
      (sourceBaseChangeIso f f' e he b) (pullback.fst b f')
      (sourceBaseChangeIso_hom_fst f f' e he b) (isPullback_rawCompactificationOpen C b) hp
      (sourceBaseChange_transportOpen f f' e he b C) Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
