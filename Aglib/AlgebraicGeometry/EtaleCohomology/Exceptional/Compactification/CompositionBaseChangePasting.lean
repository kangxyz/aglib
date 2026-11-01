/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageCompositionExchangeFaces
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.HorizontalCoherence

/-! # Original open and proper compositor faces for composition base change -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wA wB wC wA' wB' wC'

variable (Λ : Type (u + 1)) [Ring Λ]
  {A B C A' B' C' : Scheme.{u}}
  [HasDerivedCategory.{wA} (ModuleSheaf A Λ)]
  [HasDerivedCategory.{wB} (ModuleSheaf B Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]
  [HasDerivedCategory.{wA'} (ModuleSheaf A' Λ)]
  [HasDerivedCategory.{wB'} (ModuleSheaf B' Λ)]
  [HasDerivedCategory.{wC'} (ModuleSheaf C' Λ)]

/-- Actual Cartesian open pasting, in the contraction orientation used by the
original exceptional compositor, with both original source equalities. -/
theorem moduleDerivedOpenComposition_baseChange
    (k : A ⟶ B) (l : B ⟶ C) (j : A ⟶ C) (hj : k ≫ l = j)
    (k' : A' ⟶ B') (l' : B' ⟶ C') (j' : A' ⟶ C') (hj' : k' ≫ l' = j')
    (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
    [Etale k] [Etale l] [Etale j] [Etale k'] [Etale l'] [Etale j']
    (hk : IsPullback a k' k b) (hl : IsPullback b l' l c)
    (h : IsPullback a j' j c) :
    ImageCompositionOpenExchange
      ((moduleDerivedLowerShriekCompIso Λ l k).symm ≪≫
        eqToIso (moduleDerivedLowerShriek_congr Λ hj))
      ((moduleDerivedLowerShriekCompIso Λ l' k').symm ≪≫
        eqToIso (moduleDerivedLowerShriek_congr Λ hj'))
      (moduleDerivedLowerShriekCartesianBaseChangeIso a k' k b hk Λ)
      (moduleDerivedLowerShriekCartesianBaseChangeIso a j' j c h Λ)
      (moduleDerivedLowerShriekCartesianBaseChangeIso b l' l c hl Λ) := by
  subst j
  subst j'
  simpa only [eqToIso_refl, Iso.trans_refl] using
    imageCompositionOpenExchange_of_horizontal
      (moduleDerivedLowerShriekCompIso Λ l k) (moduleDerivedLowerShriekCompIso Λ l' k')
      (moduleDerivedLowerShriekCartesianBaseChangeIso a k' k b hk Λ)
      (moduleDerivedLowerShriekCartesianBaseChangeIso a (k' ≫ l') (k ≫ l) c h Λ)
      (moduleDerivedLowerShriekCartesianBaseChangeIso b l' l c hl Λ)
      (moduleDerivedOpenComparison_hComp Λ l k l' k' c b a hl hk h)

/-- The original direct-image exchange pasting gives the proper-compositor
face. Commutativity suffices; the two right exchanges need not be invertible. -/
theorem moduleDerivedProperComposition_baseChange
    (r : A ⟶ B) (p : B ⟶ C) (r' : A' ⟶ B') (p' : B' ⟶ C')
    (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
    (hr : r' ≫ b = a ≫ r) (hp : p' ≫ c = b ≫ p)
    (h : (r' ≫ p') ≫ c = a ≫ (r ≫ p)) :
    ImageCompositionProperExchange
      (moduleDerivedDirectImageCompIso Λ p r).symm
      (moduleDerivedDirectImageCompIso Λ p' r').symm
      (moduleDerivedBaseChangeMap Λ r r' b a hr)
      (moduleDerivedBaseChangeMap Λ p p' c b hp)
      (moduleDerivedBaseChangeMap Λ (r ≫ p) (r' ≫ p') c a h) :=
  imageCompositionProperExchange_of_pasting
    (moduleDerivedDirectImageCompIso Λ p r) (moduleDerivedDirectImageCompIso Λ p' r')
    (moduleDerivedBaseChangeMap Λ r r' b a hr)
    (moduleDerivedBaseChangeMap Λ p p' c b hp)
    (moduleDerivedBaseChangeMap Λ (r ≫ p) (r' ≫ p') c a h)
    (moduleDerivedBaseChangeMap_vComp Λ p r p' r' c b a hp hr h)

end AlgebraicGeometry.Scheme.EtaleCohomology
