/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawBaseChangeIterationPasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.NormalizedBaseChangeIteration
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawTargetIso
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawSourceIsoPasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawSquareCongruence
public import Aglib.CategoryTheory.NatTrans.RefinedSourcePasting

/-! # Actual source and ambient associators identify the original iterated raw exchange -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients Hom.DenseCompactification

universe u wX wS wM wXs wU wMs wXi wMi
variable {X S T U : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (C : Hom.DenseCompactification f) (b : T ⟶ S) (c : U ⟶ T)

omit [QuasiCompact f] in
private theorem isPullback_iterationSourceOpen :
    IsPullback ((iteratedSourceIso (f := f) b c).hom ≫ pullback.snd (c ≫ b) f)
      (iterationSingleRawModel b c C).j C.j (pullback.snd (c ≫ b) C.p) := by
  have ht := (isPullback_sourceIsoOpen (iteratedSourceIso (f := f) b c)
      (C.toCompactification.baseChange (c ≫ b)).j).paste_horiz
        (isPullback_rawCompactificationOpen C.toCompactification (c ≫ b))
  have hq : (𝟙 (C.toCompactification.baseChange (c ≫ b)).Xbar) ≫
      (show (C.toCompactification.baseChange (c ≫ b)).Xbar ⟶ C.Xbar from
        pullback.snd (c ≫ b) C.p) = pullback.snd (c ≫ b) C.p := Category.id_comp _
  rw [hq] at ht
  exact ht

omit [QuasiCompact f] in
private theorem isPullback_iterationCompositeSourceOpen :
    IsPullback (pullback.snd c (pullback.fst b f) ≫ pullback.snd b f)
      (iterationSingleRawModel b c C).j C.j (pullback.snd (c ≫ b) C.p) := by
  simpa only [iteratedSourceIso_hom_snd] using isPullback_iterationSourceOpen C b c

variable (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wXs} (ModuleSheaf (pullback (c ≫ b) f) Λ)]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wMs}
    (ModuleSheaf (C.toCompactification.baseChange (c ≫ b)).Xbar Λ)]
  [HasDerivedCategory.{wXi} (ModuleSheaf (pullback c (pullback.fst b f)) Λ)]
  [HasDerivedCategory.{wMi}
    (ModuleSheaf ((C.toCompactification.baseChange b).baseChange c).Xbar Λ)]

local instance rawIterationSinglePullbackModel :
    HasDerivedCategory.{wMs} (ModuleSheaf (pullback (c ≫ b) C.p) Λ) :=
  inferInstanceAs
    (HasDerivedCategory.{wMs} (ModuleSheaf (C.toCompactification.baseChange (c ≫ b)).Xbar Λ))
local instance rawIterationSingleTransportModel :
    HasDerivedCategory.{wMs} (ModuleSheaf (iterationSingleRawModel b c C).Xbar Λ) :=
  inferInstanceAs
    (HasDerivedCategory.{wMs} (ModuleSheaf (C.toCompactification.baseChange (c ≫ b)).Xbar Λ))

/-- The native source compositor includes the actual source associator projection equation. -/
def moduleRawIterationSourceIso :
    moduleDerivedInverseImageTorsion
        (pullback.snd c (pullback.fst b f) ≫ pullback.snd b f) Λ ≅
      moduleDerivedInverseImageTorsion (pullback.snd (c ≫ b) f) Λ ⋙
        moduleDerivedInverseImageTorsion (iteratedSourceIso (f := f) b c).hom Λ :=
  eqToIso (congrArg (fun z => moduleDerivedInverseImageTorsion z Λ)
      (iteratedSourceIso_hom_snd (f := f) b c).symm) ≪≫
    moduleDerivedInverseImageTorsionCompIso Λ (pullback.snd (c ≫ b) f)
      (iteratedSourceIso (f := f) b c).hom

/-- The original transition along the actual native ambient pullback associator. -/
def moduleRawIterationAmbientTransition :
    moduleRawCompactificationFunctor (iterationSingleRawModel b c C) Λ ⟶
      moduleRawCompactificationFunctor ((C.toCompactification.baseChange b).baseChange c) Λ :=
  moduleRawCompactificationTransition ((C.toCompactification.baseChange b).baseChange c)
    (iterationSingleRawModel b c C) (iterationRawAmbientIso b c C).hom
    (isPullback_iterationRawAmbientIso b c C) (iterationRawAmbientIso_hom_p b c C) Λ

omit [QuasiCompact f] in
/-- Literal iterated raw exchange is identified with one-step raw exchange by
the actual source and ambient associators and their original comparison maps. -/
theorem moduleRawIterationCompositeMap_source_pasting :
    RefinedSourceIsoPastingEquation
      (moduleRawCompactificationBaseChangeIso C.toCompactification (c ≫ b) Λ).hom
      (moduleRawIterationCompositeMap C.toCompactification b c Λ)
      (moduleRawIterationSourceIso b c Λ)
      (moduleRawCompactificationSourceIso (iteratedSourceIso (f := f) b c) Λ
        (pullback.fst c (pullback.fst b f)) (iteratedSourceIso_hom_fst b c)
        (C.toCompactification.baseChange (c ≫ b)))
      (moduleRawIterationAmbientTransition C b c Λ) := by
  let a := pullback.snd c (pullback.fst b f) ≫ pullback.snd b f
  let a' := (iteratedSourceIso (f := f) b c).hom ≫ pullback.snd (c ≫ b) f
  let D := C.toCompactification.baseChange (c ≫ b)
  let E := iterationSingleRawModel b c C
  let I := (C.toCompactification.baseChange b).baseChange c
  let q := pullback.snd (c ≫ b) C.p
  let hp := (IsPullback.of_hasPullback (c ≫ b) C.p).flip
  exact refinedSourceIsoPasting_of_equations
    (moduleRawSquareMap C.toCompactification D (pullback.snd (c ≫ b) f) q (c ≫ b)
      (isPullback_rawCompactificationOpen C.toCompactification (c ≫ b)) hp Λ)
    (moduleRawSquareMap C.toCompactification E a' q (c ≫ b)
      (isPullback_iterationSourceOpen C b c) hp Λ)
    (moduleRawSquareMap C.toCompactification E a q (c ≫ b)
      (isPullback_iterationCompositeSourceOpen C b c) hp Λ)
    (moduleRawIterationCompositeMap C.toCompactification b c Λ)
    (eqToIso (congrArg (fun z => moduleDerivedInverseImageTorsion z Λ)
      (iteratedSourceIso_hom_snd (f := f) b c).symm))
    (moduleDerivedInverseImageTorsionCompIso Λ (pullback.snd (c ≫ b) f)
      (iteratedSourceIso (f := f) b c).hom)
    (moduleRawCompactificationSourceIso (iteratedSourceIso (f := f) b c) Λ
      (pullback.fst c (pullback.fst b f)) (iteratedSourceIso_hom_fst b c) D)
    (moduleRawIterationAmbientTransition C b c Λ)
    (moduleRawSquareMap_targetIso C.toCompactification I E a
      (pullback.snd c (C.toCompactification.baseChange b).p ≫ pullback.snd b C.p)
      q (c ≫ b) (iterationRawAmbientIso b c C).hom
      (isPullback_iterationRawAmbientIso b c C) (iterationRawAmbientIso_hom_p b c C)
      (pullbackRightPullbackFstIso_hom_snd b C.p c)
      (isPullback_rawIterationOpen C.toCompactification b c)
      (isPullback_iterationCompositeSourceOpen C b c)
      (isPullback_rawIterationProper C.toCompactification b c) hp Λ)
    (moduleRawSquareMap_congr_source C.toCompactification E a a'
      (iteratedSourceIso_hom_snd (f := f) b c).symm q (c ≫ b)
      (isPullback_iterationCompositeSourceOpen C b c) (isPullback_iterationSourceOpen C b c) hp Λ)
    (moduleRawSquareMap_sourceIso_pasting C.toCompactification D (pullback.snd (c ≫ b) f)
      q (c ≫ b) (iteratedSourceIso (f := f) b c) (pullback.fst c (pullback.fst b f))
      (iteratedSourceIso_hom_fst b c)
      (isPullback_rawCompactificationOpen C.toCompactification (c ≫ b)) hp
      (isPullback_iterationSourceOpen C b c) Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
