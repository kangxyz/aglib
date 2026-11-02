/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChangeComposition
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

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The original chosen horizontal law, displaying every native associator. -/
theorem moduleExceptionalDirectImageUnboundedSuppliedCompIso_cartesianBaseChange_iso :
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
    Functor.isoWhiskerRight (moduleExceptionalDirectImageUnboundedSuppliedCompIso f g Λ N hN hΛ)
        (moduleUnboundedDerivedInverseImage Λ c) ≪≫
      moduleExceptionalDirectImageUnboundedCartesianBaseChangeIsoOfNonempty
        (f ≫ g) (f' ≫ g') c a (sqf.paste_vert sqg) Λ N hN hΛ =
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (moduleExceptionalDirectImageUnboundedOfNonempty f Λ)
        (moduleExceptionalDirectImageUnboundedCartesianBaseChangeIsoOfNonempty
          g g' c b sqg Λ N hN hΛ) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (moduleExceptionalDirectImageUnboundedCartesianBaseChangeIsoOfNonempty
          f f' b a sqf Λ N hN hΛ) (moduleExceptionalDirectImageUnboundedOfNonempty g' Λ) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ a)
        (moduleExceptionalDirectImageUnboundedSuppliedCompIso f' g' Λ N hN hΛ) := by
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
    (moduleExceptionalDirectImageUnboundedSuppliedCompIso_cartesianBaseChange f g f' g' a b c
      sqf sqg C Λ N hN hΛ)

variable [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]

/-- On the original qcqs domain this is literally the original chosen κ;
the arbitrary new base still requires no qcqs assumption. -/
theorem moduleExceptionalDirectImageUnboundedCompIso_cartesianBaseChange :
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
      (moduleExceptionalDirectImageUnboundedCompIso f g Λ N hN hΛ)
      (moduleExceptionalDirectImageUnboundedSuppliedCompIso f' g' Λ N hN hΛ)
      (moduleExceptionalDirectImageUnboundedCartesianBaseChangeIsoOfNonempty
        f f' b a sqf Λ N hN hΛ).hom
      (moduleExceptionalDirectImageUnboundedCartesianBaseChangeIsoOfNonempty
        g g' c b sqg Λ N hN hΛ).hom
      (moduleExceptionalDirectImageUnboundedCartesianBaseChangeIsoOfNonempty
        (f ≫ g) (f' ≫ g') c a (sqf.paste_vert sqg) Λ N hN hΛ).hom := by
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
  exact moduleExceptionalDirectImageUnboundedSuppliedCompIso_cartesianBaseChange f g f' g' a b c
    sqf sqg C Λ N hN hΛ

end AlgebraicGeometry.Scheme.EtaleCohomology
