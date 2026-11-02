/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionBaseChangeCube
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionBaseChangePasting

/-! # The original compactified composition map commutes with exchange

The geometric proper faces need only commute. Its open faces are genuinely
Cartesian. This is useful for dense normalized towers, whose proper faces are
not incorrectly asserted to remain Cartesian after schematic-image refinement.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wA wB wY wC wZ wX' wA' wB' wY' wC' wZ'

variable (Λ : Type (u + 1)) [Ring Λ]
  {X A B Y C Z X' A' B' Y' C' Z' : Scheme.{u}}
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wA} (ModuleSheaf A Λ)]
  [HasDerivedCategory.{wB} (ModuleSheaf B Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wA'} (ModuleSheaf A' Λ)]
  [HasDerivedCategory.{wB'} (ModuleSheaf B' Λ)]
  [HasDerivedCategory.{wY'} (ModuleSheaf Y' Λ)]
  [HasDerivedCategory.{wC'} (ModuleSheaf C' Λ)]
  [HasDerivedCategory.{wZ'} (ModuleSheaf Z' Λ)]
  (k : X ⟶ A) (m : A ⟶ B) (j : X ⟶ B) (q : A ⟶ Y)
  (i : Y ⟶ C) (r : B ⟶ C) (p : C ⟶ Z)
  (k' : X' ⟶ A') (m' : A' ⟶ B') (j' : X' ⟶ B') (q' : A' ⟶ Y')
  (i' : Y' ⟶ C') (r' : B' ⟶ C') (p' : C' ⟶ Z')
  [Etale k] [Etale m] [Etale j] [Etale i]
  [Etale k'] [Etale m'] [Etale j'] [Etale i']
  (hk : k ≫ m = j) (hk' : k' ≫ m' = j')
  (sq : IsPullback q m i r) (sq' : IsPullback q' m' i' r')
  (a : X' ⟶ X) (aA : A' ⟶ A) (aB : B' ⟶ B)
  (b : Y' ⟶ Y) (bC : C' ⟶ C) (c : Z' ⟶ Z)
  (sqk : IsPullback a k' k aA) (sqj : IsPullback a j' j aB)
  (sqm : IsPullback aA m' m aB) (sqi : IsPullback b i' i bC)
  (hq : q' ≫ b = aA ≫ q) (hr : r' ≫ bC = aB ≫ r)
  (hp : p' ≫ c = bC ≫ p) (ht : (r' ≫ p') ≫ c = aB ≫ (r ≫ p))

include hr sqm in
/-- The genuine original model composition-exchange square, proved from the
original mate and compositor laws with twelve independent derived models. -/
theorem moduleUnboundedCompactifiedComposition_exchange :
    ImageCompositionExchangeEquation
      (imageCompositionMap (moduleUnboundedProperOpenMate q m i r sq Λ)
      ((moduleUnboundedDerivedLowerShriekCompIso Λ m k).symm ≪≫
        eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ hk))
      (moduleUnboundedDerivedDirectImageCompIso Λ p r).symm) (imageCompositionMap
      (moduleUnboundedProperOpenMate q' m' i' r' sq' Λ)
        ((moduleUnboundedDerivedLowerShriekCompIso Λ m' k').symm ≪≫
        eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ hk'))
      (moduleUnboundedDerivedDirectImageCompIso Λ p' r').symm)
      (moduleUnboundedDerivedBaseChangeMap Λ q q' b aA hq)
      (moduleUnboundedDerivedBaseChangeMap Λ p p' c bC hp)
      (moduleUnboundedDerivedBaseChangeMap Λ (r ≫ p) (r' ≫ p') c aB ht)
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a k' k aA sqk Λ)
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso b i' i bC sqi Λ)
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a j' j aB sqj Λ) :=
  imageCompositionExchangeEquation (moduleUnboundedProperOpenMate q m i r sq Λ)
      (moduleUnboundedProperOpenMate q' m' i' r' sq' Λ)
        ((moduleUnboundedDerivedLowerShriekCompIso Λ m k).symm ≪≫
        eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ hk))
      ((moduleUnboundedDerivedLowerShriekCompIso Λ m' k').symm ≪≫
        eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ hk'))
      (moduleUnboundedDerivedDirectImageCompIso Λ p r).symm
        (moduleUnboundedDerivedDirectImageCompIso Λ p' r').symm
    (moduleUnboundedDerivedBaseChangeMap Λ q q' b aA hq)
    (moduleUnboundedDerivedBaseChangeMap Λ r r' bC aB hr)
    (moduleUnboundedDerivedBaseChangeMap Λ p p' c bC hp)
    (moduleUnboundedDerivedBaseChangeMap Λ (r ≫ p) (r' ≫ p') c aB ht)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a k' k aA sqk Λ)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a j' j aB sqj Λ)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso aA m' m aB sqm Λ)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso b i' i bC sqi Λ)
    (imageCompositionMap (moduleUnboundedProperOpenMate q m i r sq Λ)
      ((moduleUnboundedDerivedLowerShriekCompIso Λ m k).symm ≪≫
        eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ hk))
      (moduleUnboundedDerivedDirectImageCompIso Λ p r).symm) (imageCompositionMap
      (moduleUnboundedProperOpenMate q' m' i' r' sq' Λ)
        ((moduleUnboundedDerivedLowerShriekCompIso Λ m' k').symm ≪≫
        eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ hk'))
      (moduleUnboundedDerivedDirectImageCompIso Λ p' r').symm)
    (imageCompositionMap_formula (moduleUnboundedProperOpenMate q m i r sq Λ)
      ((moduleUnboundedDerivedLowerShriekCompIso Λ m k).symm ≪≫
        eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ hk))
      (moduleUnboundedDerivedDirectImageCompIso Λ p r).symm) (imageCompositionMap_formula
      (moduleUnboundedProperOpenMate q' m' i' r' sq' Λ)
        ((moduleUnboundedDerivedLowerShriekCompIso Λ m' k').symm ≪≫
        eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ hk'))
      (moduleUnboundedDerivedDirectImageCompIso Λ p' r').symm)
    (moduleUnboundedProperOpenMate_baseChange i m q r i' m' q' r' b aA bC aB
      sq sq' sqi sqm hq hr Λ)
    (moduleUnboundedDerivedOpenComposition_baseChange Λ k m j hk k' m' j' hk' a aA aB
      sqk sqm sqj)
    (moduleUnboundedDerivedProperComposition_baseChange Λ r p r' p' aB bC c hr hp ht)

end AlgebraicGeometry.Scheme.EtaleCohomology
