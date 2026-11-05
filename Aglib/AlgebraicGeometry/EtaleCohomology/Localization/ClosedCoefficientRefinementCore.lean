/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.CohomologySquare
public import Aglib.CategoryTheory.Adjunction.Mates.CoefficientPasting
public import Aglib.CategoryTheory.Sites.SheafCohomology.MapDiagram
public import Aglib.CategoryTheory.Sites.SheafCohomology.MapIsoInjection
public import Aglib.Logic.Function.RefinementDiagram

/-! # Original square-coefficient refinement before coefficient specialization

The entire diagram is proved for original abelian sheaves and an original
coefficient arrow. Categorical pasting and cohomology-function evaluation are
performed over variable categories and carriers before inserting these maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u eT eW eT₂ eW₂

attribute [local instance] hasSheafifyLarge

variable {X Z T W T₂ W₂ : Scheme.{u}}
  (i : Z ⟶ X) (i' : W ⟶ T) (i₂ : W₂ ⟶ T₂)
  (b : T ⟶ X) (b' : W ⟶ Z) (t : T₂ ⟶ T) (t' : W₂ ⟶ W)
  (h : i' ≫ b = b' ≫ i) (ht : i₂ ≫ t = t' ≫ i')
  (hcomp : i₂ ≫ (t ≫ b) = (t' ≫ b') ≫ i)
  (F : AbelianSheaf.{u, u + 1} X) (A : AbelianSheaf.{u, u + 1} Z)
  (c : (inverseImage i).obj F ⟶ A)

/-- The actual inverse-image square with an appended coefficient arrow
satisfies the full canonical target-refinement equation. -/
theorem inverseImageSquareIso_coefficient_refinement :
    (inverseImage i₂).map ((inverseImageComp b t).hom.app F) ≫
        (inverseImageSquareIso i' i₂ t t' ht).hom.app ((inverseImage b).obj F) ≫
        (inverseImage t').map
          ((inverseImageSquareIso i i' b b' h).hom.app F ≫ (inverseImage b').map c) =
      ((inverseImageSquareIso i i₂ (t ≫ b) (t' ≫ b') hcomp).hom.app F ≫
          (inverseImage (t' ≫ b')).map c) ≫
        (inverseImageComp b' t').hom.app A :=
  horizontalSquareEquation_coefficient
    (TwoSquare.mk _ _ _ _ (inverseImageSquareIso i i' b b' h).hom)
    (TwoSquare.mk _ _ _ _ (inverseImageSquareIso i' i₂ t t' ht).hom)
    (TwoSquare.mk _ _ _ _ (inverseImageSquareIso i i₂ (t ≫ b) (t' ≫ b') hcomp).hom)
    (inverseImageComp b t).hom (inverseImageComp b' t').hom F A c
    (inverseImageSquareIso_hComp i i' i₂ b t b' t' h ht hcomp F)

variable [HasExt.{eT} (AbelianSheaf.{u, u + 1} T)]
  [HasExt.{eW} (AbelianSheaf.{u, u + 1} W)]
  [HasExt.{eT₂} (AbelianSheaf.{u, u + 1} T₂)]
  [HasExt.{eW₂} (AbelianSheaf.{u, u + 1} W₂)]

include ht

/-- The full original class equation is evaluated by the generic refinement
calculation, supplied with the actual original square and naturality laws. -/
theorem inverseImageSquareIso_coefficientClass_refinement
    (q : ℕ) (x : Sheaf.H.{eT} ((inverseImage b).obj F) q) :
    Sheaf.H.map ((inverseImageComp b' t').hom.app A) q
        (Sheaf.H.map
          ((inverseImageSquareIso i i₂ (t ≫ b) (t' ≫ b') hcomp).hom.app F ≫
            (inverseImage (t' ≫ b')).map c) q
          (cohomologyPullback i₂ _ q
            (Sheaf.H.map ((inverseImageComp b t).inv.app F) q
              (cohomologyPullback t _ q x)))) =
      cohomologyPullback t' _ q
        (Sheaf.H.map
          ((inverseImageSquareIso i i' b b' h).hom.app F ≫ (inverseImage b').map c) q
          (cohomologyPullback i' _ q x)) := by
  let γ : (inverseImage (t ≫ b)).obj F ≅
      (inverseImage t).obj ((inverseImage b).obj F) :=
    (inverseImageComp b t).app F
  let K := (inverseImageSquareIso i i' b b' h).hom.app F ≫ (inverseImage b').map c
  let K₂ := (inverseImageSquareIso i i₂ (t ≫ b) (t' ≫ b') hcomp).hom.app F ≫
    (inverseImage (t' ≫ b')).map c
  let S := (inverseImageSquareIso i' i₂ t t' ht).hom.app ((inverseImage b).obj F)
  let δ := (inverseImageComp b' t').hom.app A
  have hcancel := Function.comparison_cancel
    (Sheaf.H.map γ.hom q) (Sheaf.H.map γ.inv q)
    (cohomologyPullback i₂ ((inverseImage (t ≫ b)).obj F) q)
    (cohomologyPullback i₂ ((inverseImage t).obj ((inverseImage b).obj F)) q)
    (Sheaf.H.map ((inverseImage i₂).map γ.hom) q)
    (Sheaf.H.map_iso_inv_hom_apply γ q)
    (fun z => (cohomologyPullback_coefficientMap i₂ γ.hom q z).symm)
  exact Function.refinement_diagram_apply
    (cohomologyPullback t ((inverseImage b).obj F) q) (Sheaf.H.map γ.inv q)
    (cohomologyPullback i₂ ((inverseImage (t ≫ b)).obj F) q)
    (Sheaf.H.map ((inverseImage i₂).map γ.hom) q)
    (cohomologyPullback i₂ ((inverseImage t).obj ((inverseImage b).obj F)) q)
    (Sheaf.H.map S q) (cohomologyPullback i' ((inverseImage b).obj F) q)
    (cohomologyPullback t' ((inverseImage i').obj ((inverseImage b).obj F)) q)
    (Sheaf.H.map K q) (cohomologyPullback t' ((inverseImage b').obj A) q)
    (Sheaf.H.map K₂ q) (Sheaf.H.map δ q)
    (Sheaf.H.map ((inverseImage t').map K) q)
    hcancel (cohomologyPullback_square i' i₂ t t' ht ((inverseImage b).obj F) q)
    (Sheaf.H.map_three_factorization ((inverseImage i₂).map γ.hom) S
      ((inverseImage t').map K) K₂ δ
      (inverseImageSquareIso_coefficient_refinement i i' i₂ b b' t t' h ht hcomp F A c) q)
    (fun z => (cohomologyPullback_coefficientMap t' K q z).symm) x

/-- Refined square-coefficient zero is equivalent to zero of the actual
pullback of the original transformed class. -/
theorem inverseImageSquareIso_coefficientClass_refinement_eq_zero_iff
    (q : ℕ) (x : Sheaf.H.{eT} ((inverseImage b).obj F) q) :
    Sheaf.H.map
        ((inverseImageSquareIso i i₂ (t ≫ b) (t' ≫ b') hcomp).hom.app F ≫
          (inverseImage (t' ≫ b')).map c) q
        (cohomologyPullback i₂ _ q
          (Sheaf.H.map ((inverseImageComp b t).inv.app F) q
            (cohomologyPullback t _ q x))) = 0 ↔
      cohomologyPullback t' _ q
        (Sheaf.H.map
          ((inverseImageSquareIso i i' b b' h).hom.app F ≫ (inverseImage b').map c) q
          (cohomologyPullback i' _ q x)) = 0 := by
  have he := inverseImageSquareIso_coefficientClass_refinement
    i i' i₂ b b' t t' h ht hcomp F A c q x
  constructor
  · intro hz
    rw [← he, hz, map_zero]
  · intro hz
    apply Sheaf.H.map_injective_of_isIso ((inverseImageComp b' t').hom.app A) q
    rw [map_zero, he]
    exact hz

end AlgebraicGeometry.Scheme.EtaleCohomology
