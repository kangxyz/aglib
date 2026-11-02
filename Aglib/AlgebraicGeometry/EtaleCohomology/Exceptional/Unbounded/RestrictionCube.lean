/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.InverseImageCube
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChange
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactMateCube

/-! # The actual unbounded exchange commutes with restriction

All six inverse-image faces are localized on every complex. The original
four adjunction mates then yield the actual restriction cube for direct-image
exchange. No bounded-below testing or homology faithfulness is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wX' wS' wY wT wY' wT'

variable (Λ : Type (u + 1)) [Ring Λ]

section Factor
variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S' Λ)]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- The actual unbounded inverse-image square retains its original complex factor. -/
theorem moduleUnboundedDerivedInverseImageSquareIso_exactFactor
    (K : CochainComplex (ModuleSheaf S Λ) ℤ) :
    ExactFactorSquareEquation (moduleInverseImage f Λ) (moduleInverseImage g' Λ)
      (moduleInverseImage g Λ) (moduleInverseImage f' Λ)
      (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f f' g g' h).hom)
      (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ f f' g g' h).hom) K :=
  mapDerivedCategorySquareIso_exactFactor
    (moduleInverseImage f Λ) (moduleInverseImage g' Λ)
    (moduleInverseImage g Λ) (moduleInverseImage f' Λ)
    (moduleInverseImageSquareIso Λ f f' g g' h)
    (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ f f' g g' h).hom)
    rfl K

end Factor

variable {X S X' S' Y T Y' T' : Scheme.{u}}
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S' Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wY'} (ModuleSheaf Y' Λ)]
  [HasDerivedCategory.{wT'} (ModuleSheaf T' Λ)]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (p : Y ⟶ T) (p' : Y' ⟶ T') (q : T' ⟶ T) (q' : Y' ⟶ Y)
  (jS : T ⟶ S) (jX : Y ⟶ X) (jS' : T' ⟶ S') (jX' : Y' ⟶ X')
  (hf : p ≫ jS = jX ≫ f) (hf' : p' ≫ jS' = jX' ≫ f')
  (hg : q ≫ jS = jS' ≫ g) (hg' : q' ≫ jX = jX' ≫ g')
  (h : f' ≫ g = g' ≫ f) (h' : p' ≫ q = q' ≫ p)

/-- The same original direct-image exchanges form the actual restriction cube. -/
theorem moduleUnboundedDerivedBaseChangeMap_restriction_cube :
    HorizontalMateCubeEquation
      (moduleUnboundedDerivedBaseChangeMap Λ f p jS jX hf)
      (moduleUnboundedDerivedBaseChangeMap Λ f' p' jS' jX' hf')
      (moduleUnboundedDerivedBaseChangeMap Λ f f' g g' h)
      (moduleUnboundedDerivedBaseChangeMap Λ p p' q q' h')
      (moduleUnboundedDerivedInverseImageSquareIso Λ g q jS jS' hg).hom
      (moduleUnboundedDerivedInverseImageSquareIso Λ g' q' jX jX' hg').hom :=
  mapDerivedCategory_mateCube_of_whole
    (moduleUnboundedDerivedAdjunction Λ f) (moduleUnboundedDerivedAdjunction Λ f')
    (moduleUnboundedDerivedAdjunction Λ p) (moduleUnboundedDerivedAdjunction Λ p')
    (moduleInverseImageSquareIso Λ f p jS jX hf).symm
    (moduleInverseImageSquareIso Λ f' p' jS' jX' hf').symm
    (moduleInverseImageSquareIso Λ g q jS jS' hg).symm
    (moduleInverseImageSquareIso Λ g' q' jX jX' hg').symm
    (moduleInverseImageSquareIso Λ f f' g g' h)
    (moduleInverseImageSquareIso Λ p p' q q' h')
    (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ f p jS jX hf).hom)
    (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ f' p' jS' jX' hf').hom)
    (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ f f' g g' h).hom)
    (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ p p' q q' h').hom)
    (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ g q jS jS' hg).hom)
    (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ g' q' jX jX' hg').hom)
    (moduleUnboundedDerivedInverseImageSquareIso_exactFactor Λ f p jS jX hf)
    (moduleUnboundedDerivedInverseImageSquareIso_exactFactor Λ f' p' jS' jX' hf')
    (moduleUnboundedDerivedInverseImageSquareIso_exactFactor Λ f f' g g' h)
    (moduleUnboundedDerivedInverseImageSquareIso_exactFactor Λ p p' q q' h')
    (moduleUnboundedDerivedInverseImageSquareIso_exactFactor Λ g q jS jS' hg)
    (moduleUnboundedDerivedInverseImageSquareIso_exactFactor Λ g' q' jX jX' hg')
    (moduleInverseImageSquareIso_restriction_cube Λ f f' g g' p p' q q'
      jS jX jS' jX' hf hf' hg hg' h h')
    (moduleUnboundedDerivedBaseChangeMap Λ f p jS jX hf)
    (moduleUnboundedDerivedBaseChangeMap Λ f' p' jS' jX' hf')
    (moduleUnboundedDerivedBaseChangeMap Λ f f' g g' h)
    (moduleUnboundedDerivedBaseChangeMap Λ p p' q q' h')
    rfl rfl rfl rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
