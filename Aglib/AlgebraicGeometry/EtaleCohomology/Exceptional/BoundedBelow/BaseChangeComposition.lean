/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.CompositionBaseChangeFaces
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionBCModelComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.SuppliedComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.CompositionBCModelSquare

/-! # Original chosen exceptional base change and binary composition

The actual normalized tower supplies every model square. No qcqs hypothesis on
any new base and no desired exchange cube is supplied as a premise.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wY wZ wX' wY' wZ' wLF wLG wLH
  wF wG wH wF' wG' wH' wNF wNG wNH wRF wRG wRH
variable {X Y Z X' Y' Z' : Scheme.{u}}
  (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
  [QuasiCompact f] [QuasiCompact g] [QuasiCompact f'] [QuasiCompact g']
  (a : X' ⟶ X) (b : Y' ⟶ Y) (c : Z' ⟶ Z)
  (sqf : IsPullback a f' f b) (sqg : IsPullback b g' g c)
  (C : Hom.CompactifiedComposition f g)
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [hZ : HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [hXprime : HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [hYprime : HasDerivedCategory.{wY'} (ModuleSheaf Y' Λ)]
  [hZprime : HasDerivedCategory.{wZ'} (ModuleSheaf Z' Λ)]
  [hLF : HasDerivedCategory.{wLF} (ModuleSheaf (pullback b f) Λ)]
  [hLG : HasDerivedCategory.{wLG} (ModuleSheaf (pullback c g) Λ)]
  [hLH : HasDerivedCategory.{wLH} (ModuleSheaf (pullback c (f ≫ g)) Λ)]
  [fm : ∀ E : Hom.DenseCompactification f,
    HasDerivedCategory.{wF} (ModuleSheaf E.Xbar Λ)]
  [gm : ∀ E : Hom.DenseCompactification g,
    HasDerivedCategory.{wG} (ModuleSheaf E.Xbar Λ)]
  [hm : ∀ E : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wH} (ModuleSheaf E.Xbar Λ)]
  [fmp : ∀ E : Hom.DenseCompactification f',
    HasDerivedCategory.{wF'} (ModuleSheaf E.Xbar Λ)]
  [gmp : ∀ E : Hom.DenseCompactification g',
    HasDerivedCategory.{wG'} (ModuleSheaf E.Xbar Λ)]
  [hmp : ∀ E : Hom.DenseCompactification (f' ≫ g'),
    HasDerivedCategory.{wH'} (ModuleSheaf E.Xbar Λ)]
  [fn : ∀ E : Hom.DenseCompactification (pullback.fst b f),
    HasDerivedCategory.{wNF} (ModuleSheaf E.Xbar Λ)]
  [gn : ∀ E : Hom.DenseCompactification (pullback.fst c g),
    HasDerivedCategory.{wNG} (ModuleSheaf E.Xbar Λ)]
  [hn : ∀ E : Hom.DenseCompactification (pullback.fst c (f ≫ g)),
    HasDerivedCategory.{wNH} (ModuleSheaf E.Xbar Λ)]
  [fr : ∀ E : Hom.DenseCompactification f,
    HasDerivedCategory.{wRF} (ModuleSheaf (pullback b E.p) Λ)]
  [gr : ∀ E : Hom.DenseCompactification g,
    HasDerivedCategory.{wRG} (ModuleSheaf (pullback c E.p) Λ)]
  [hr : ∀ E : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wRH} (ModuleSheaf (pullback c E.p) Λ)]

/-- The original chosen Cartesian exchanges commute with the original supplied
compositors for actual pasted Cartesian squares and independent model families. -/
theorem moduleExceptionalSuppliedCompositionIso_cartesianBaseChange :
    letI : Nonempty (Hom.DenseCompactification f) := ⟨C.first⟩
    letI : Nonempty (Hom.DenseCompactification g) :=
      ⟨C.targetCompactification⟩
    letI : Nonempty (Hom.DenseCompactification (f ≫ g)) :=
      ⟨C.composite⟩
    letI : Nonempty (Hom.CompactifiedComposition f g) := ⟨C⟩
    letI : Nonempty (Hom.DenseCompactification f') :=
      ⟨(C.cartesianBaseChange f' g' a b c sqf sqg).first⟩
    letI : Nonempty (Hom.DenseCompactification g') :=
      ⟨(C.cartesianBaseChange f' g' a b c sqf sqg).targetCompactification⟩
    letI : Nonempty (Hom.DenseCompactification (f' ≫ g')) :=
      ⟨(C.cartesianBaseChange f' g' a b c sqf sqg).composite⟩
    letI : Nonempty (Hom.CompactifiedComposition f' g') :=
      ⟨C.cartesianBaseChange f' g' a b c sqf sqg⟩
    CompositionExchangeEquation
      (moduleExceptionalSuppliedCompositionIso f g Λ)
      (moduleExceptionalSuppliedCompositionIso f' g' Λ)
      (moduleExceptionalDirectImagePlusTorsionCartesianBaseChangeIsoOfNonempty
        f f' b a sqf Λ).hom
      (moduleExceptionalDirectImagePlusTorsionCartesianBaseChangeIsoOfNonempty
        g g' c b sqg Λ).hom
      (moduleExceptionalDirectImagePlusTorsionCartesianBaseChangeIsoOfNonempty
        (f ≫ g) (f' ≫ g') c a (sqf.paste_vert sqg) Λ).hom := by
  let : Nonempty (Hom.DenseCompactification f) := ⟨C.first⟩
  let : Nonempty (Hom.DenseCompactification g) :=
    ⟨C.targetCompactification⟩
  let : Nonempty (Hom.DenseCompactification (f ≫ g)) :=
    ⟨C.composite⟩
  let : Nonempty (Hom.CompactifiedComposition f g) := ⟨C⟩
  let : Nonempty (Hom.DenseCompactification f') :=
    ⟨(C.cartesianBaseChange f' g' a b c sqf sqg).first⟩
  let : Nonempty (Hom.DenseCompactification g') :=
    ⟨(C.cartesianBaseChange f' g' a b c sqf sqg).targetCompactification⟩
  let : Nonempty (Hom.DenseCompactification (f' ≫ g')) :=
    ⟨(C.cartesianBaseChange f' g' a b c sqf sqg).composite⟩
  let : Nonempty (Hom.CompactifiedComposition f' g') :=
    ⟨C.cartesianBaseChange f' g' a b c sqf sqg⟩
  let D := C.cartesianBaseChange f' g' a b c sqf sqg
  let qF := C.baseChangeFirstProjection f' g' a b c sqf sqg
  let qG := C.baseChangeTargetProjection g' b c sqg
  let qH := C.baseChangeSourceProjection f' g' a b c sqf sqg
  have hjF := C.isPullback_baseChangeFirst_open f' g' a b c sqf sqg
  have hjG := C.isPullback_baseChangeTarget_open g' b c sqg
  have hjH := C.isPullback_baseChangeSource_open f' g' a b c sqf sqg
  have hpF := C.baseChangeFirstProjection_p f' g' a b c sqf sqg
  have hpG := Hom.Compactification.cartesianBaseChangeProjection_p
    C.targetCompactification.toCompactification g' b c sqg
  have hpH := C.baseChangeSourceProjection_composite_p f' g' a b c sqf sqg
  apply compositionExchangeEquation_transport
    (moduleExceptionalDirectImagePlusTorsionOfNonemptyIso f Λ C.first)
    (moduleExceptionalDirectImagePlusTorsionOfNonemptyIso g Λ C.targetCompactification)
    (moduleExceptionalDirectImagePlusTorsionOfNonemptyIso (f ≫ g) Λ C.composite)
    (moduleExceptionalDirectImagePlusTorsionOfNonemptyIso f' Λ D.first)
    (moduleExceptionalDirectImagePlusTorsionOfNonemptyIso g' Λ D.targetCompactification)
    (moduleExceptionalDirectImagePlusTorsionOfNonemptyIso (f' ≫ g') Λ D.composite)
    _ _ (moduleCompactifiedCompositionIso f g Λ C)
    (moduleCompactifiedCompositionIso f' g' Λ D) _ _ _
    (moduleCompactificationCommutingExchangeTorsion f f' C.first D.first
      a qF b hjF hpF.symm Λ)
    (moduleCompactificationCommutingExchangeTorsion g g' C.targetCompactification
      D.targetCompactification b qG c hjG hpG.symm Λ)
    (moduleCompactificationCommutingExchangeTorsion (f ≫ g) (f' ≫ g') C.composite
      D.composite a qH c hjH hpH.symm Λ)
  · exact moduleExceptionalSuppliedCompositionIso_comparison f g Λ C
  · exact moduleExceptionalSuppliedCompositionIso_comparison f' g' Λ D
  · exact moduleExceptionalCartesianBaseChange_commuting_model
      f f' b a sqf Λ C.first D.first qF hjF hpF
  · exact moduleExceptionalCartesianBaseChange_commuting_model
      g g' c b sqg Λ C.targetCompactification D.targetCompactification qG hjG hpG
  · exact moduleExceptionalCartesianBaseChange_commuting_model
      (f ≫ g) (f' ≫ g') c a (sqf.paste_vert sqg) Λ C.composite D.composite qH hjH hpH
  · exact moduleCompactifiedCompositionIso_commutingExchange
      f g f' g' C D a b c qF qG qH hjF hjG hjH
      (C.isPullback_baseChangeMiddleOpen f' g' a b c sqf sqg)
      hpF.symm hpG.symm (C.baseChangeSourceProjection_p f' g' a b c sqf sqg).symm
      hpH.symm Λ

end AlgebraicGeometry.Scheme.EtaleCohomology
