/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageCompositionExchangeFaces
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionModel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperOpenHorizontalCoherence

/-! # Original unbounded open and proper compositor faces for composition base change -/

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
theorem moduleUnboundedDerivedOpenComposition_baseChange
    (k : A ⟶ B) (l : B ⟶ C) (j : A ⟶ C) (hj : k ≫ l = j)
    (k' : A' ⟶ B') (l' : B' ⟶ C') (j' : A' ⟶ C') (hj' : k' ≫ l' = j')
    (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
    [Etale k] [Etale l] [Etale j] [Etale k'] [Etale l'] [Etale j']
    (hk : IsPullback a k' k b) (hl : IsPullback b l' l c)
    (h : IsPullback a j' j c) :
    ImageCompositionOpenExchange
      ((moduleUnboundedDerivedLowerShriekCompIso Λ l k).symm ≪≫
        eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ hj))
      ((moduleUnboundedDerivedLowerShriekCompIso Λ l' k').symm ≪≫
        eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ hj'))
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a k' k b hk Λ)
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a j' j c h Λ)
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso b l' l c hl Λ) := by
  subst j
  subst j'
  simpa only [eqToIso_refl, Iso.trans_refl] using
    imageCompositionOpenExchange_of_horizontal
      (moduleUnboundedDerivedLowerShriekCompIso Λ l k)
      (moduleUnboundedDerivedLowerShriekCompIso Λ l' k')
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a k' k b hk Λ)
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a (k' ≫ l') (k ≫ l) c h Λ)
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso b l' l c hl Λ)
      (moduleUnboundedDerivedOpenComparison_hComp Λ l k l' k' c b a hl hk h)

/-- The original direct-image exchange pasting gives the proper-compositor
face. Commutativity suffices; the two right exchanges need not be invertible. -/
theorem moduleUnboundedDerivedProperComposition_baseChange
    (r : A ⟶ B) (p : B ⟶ C) (r' : A' ⟶ B') (p' : B' ⟶ C')
    (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
    (hr : r' ≫ b = a ≫ r) (hp : p' ≫ c = b ≫ p)
    (h : (r' ≫ p') ≫ c = a ≫ (r ≫ p)) :
    ImageCompositionProperExchange
      (moduleUnboundedDerivedDirectImageCompIso Λ p r).symm
      (moduleUnboundedDerivedDirectImageCompIso Λ p' r').symm
      (moduleUnboundedDerivedBaseChangeMap Λ r r' b a hr)
      (moduleUnboundedDerivedBaseChangeMap Λ p p' c b hp)
      (moduleUnboundedDerivedBaseChangeMap Λ (r ≫ p) (r' ≫ p') c a h) :=
  imageCompositionProperExchange_of_pasting
    (moduleUnboundedDerivedDirectImageCompIso Λ p r)
    (moduleUnboundedDerivedDirectImageCompIso Λ p' r')
    (moduleUnboundedDerivedBaseChangeMap Λ r r' b a hr)
    (moduleUnboundedDerivedBaseChangeMap Λ p p' c b hp)
    (moduleUnboundedDerivedBaseChangeMap Λ (r ≫ p) (r' ≫ p') c a h)
    (moduleUnboundedDerivedBaseChangeMap_vComp Λ p r p' r' c b a hp hr h)

end AlgebraicGeometry.Scheme.EtaleCohomology
