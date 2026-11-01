/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.BaseChangeComposition
public import Aglib.CategoryTheory.Functor.CompositionExchangeIso

/-! # Original compositor recovery and fully associated base-change pasting -/

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

/-- The original chosen horizontal law, displaying every native associator. -/
theorem moduleExceptionalSuppliedCompositionIso_cartesianBaseChange_iso :
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
    Functor.isoWhiskerRight (moduleExceptionalSuppliedCompositionIso f g Λ)
        (moduleDerivedInverseImageTorsion c Λ) ≪≫
      moduleExceptionalDirectImagePlusTorsionCartesianBaseChangeIsoOfNonempty
        (f ≫ g) (f' ≫ g') c a (sqf.paste_vert sqg) Λ =
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (moduleExceptionalDirectImagePlusTorsionOfNonempty f Λ)
        (moduleExceptionalDirectImagePlusTorsionCartesianBaseChangeIsoOfNonempty
          g g' c b sqg Λ) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (moduleExceptionalDirectImagePlusTorsionCartesianBaseChangeIsoOfNonempty
          f f' b a sqf Λ) (moduleExceptionalDirectImagePlusTorsionOfNonempty g' Λ) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (moduleDerivedInverseImageTorsion a Λ)
        (moduleExceptionalSuppliedCompositionIso f' g' Λ) := by
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
  exact compositionExchangeIso _ _ _ _ _
    (moduleExceptionalSuppliedCompositionIso_cartesianBaseChange f g f' g' a b c sqf sqg C Λ)

variable [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]

/-- On the original qcqs domain this is literally the original chosen κ;
the arbitrary new base still requires no qcqs assumption. -/
theorem moduleExceptionalCompositionIso_cartesianBaseChange :
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
      (moduleExceptionalCompositionIso f g Λ)
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
  exact moduleExceptionalSuppliedCompositionIso_cartesianBaseChange f g f' g' a b c sqf sqg C Λ

end AlgebraicGeometry.Scheme.EtaleCohomology
