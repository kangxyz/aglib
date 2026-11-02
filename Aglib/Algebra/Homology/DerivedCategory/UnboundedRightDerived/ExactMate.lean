/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactAdjunction
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactSquare
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.SpecifiedMateCube
public import Aglib.Algebra.Homology.HomologicalComplex.Mates

/-! # Localization preserves original exact adjunction mates

The equation is proved on every complex by the original localization factors,
then on all derived objects by localization uniqueness. It is not inferred
from equality on homology or on bounded-below objects.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe uA vA wA uB vB wB uC vC wC uD vD wD

namespace CategoryTheory

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {G : A ⥤ C} {H : B ⥤ D}
  [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
  [G.Additive] [H.Additive]
  [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- The same two exact original squares remain mates on the native unbounded
derived categories, with independent derived-model universes. -/
theorem mapDerivedCategorySquareIso_mate
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (α : G ⋙ L₂ ≅ L₁ ⋙ H) (β : R₁ ⋙ G ≅ H ⋙ R₂)
    (h : (mateEquiv a b (TwoSquare.mk _ _ _ _ α.hom)).natTrans = β.hom) :
    (mateEquiv a.mapDerivedCategoryAdjunction b.mapDerivedCategoryAdjunction
      (TwoSquare.mk _ _ _ _ (mapDerivedCategorySquareIso L₁ H G L₂ α).hom)).natTrans =
      (mapDerivedCategorySquareIso H R₂ R₁ G β).hom := by
  let μ := (mateEquiv a.mapDerivedCategoryAdjunction b.mapDerivedCategoryAdjunction
    (TwoSquare.mk _ _ _ _ (mapDerivedCategorySquareIso L₁ H G L₂ α).hom)).natTrans
  have hc : HorizontalMateCubeEquation
      (G := G.mapHomologicalComplex (.up ℤ)) (H := H.mapHomologicalComplex (.up ℤ))
      R₁.mapDerivedCategoryFactors.inv
      R₂.mapDerivedCategoryFactors.inv (β.hom.mapHomologicalComplex (.up ℤ)) μ
      G.mapDerivedCategoryFactors.hom H.mapDerivedCategoryFactors.hom :=
    horizontalMateCubeEquation_of_specified_mates
      (G := G.mapHomologicalComplex (.up ℤ)) (H := H.mapHomologicalComplex (.up ℤ))
      (a.mapHomologicalComplex (.up ℤ)) (b.mapHomologicalComplex (.up ℤ))
      a.mapDerivedCategoryAdjunction b.mapDerivedCategoryAdjunction
      L₁.mapDerivedCategoryFactors.hom L₂.mapDerivedCategoryFactors.hom
      (α.hom.mapHomologicalComplex (.up ℤ))
      (mapDerivedCategorySquareIso L₁ H G L₂ α).hom
      G.mapDerivedCategoryFactors.hom H.mapDerivedCategoryFactors.hom
      R₁.mapDerivedCategoryFactors.inv R₂.mapDerivedCategoryFactors.inv
      (β.hom.mapHomologicalComplex (.up ℤ)) μ
      a.mapDerivedCategoryAdjunction_factor_mate b.mapDerivedCategoryAdjunction_factor_mate
      (mapHomologicalComplex_mate a b α.hom β.hom h (.up ℤ)) rfl
      (mapDerivedCategorySquareIso_fac L₁ H G L₂ α)
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso B (.up ℤ))
  intro K
  have hf := mapDerivedCategorySquareIso_fac H R₂ R₁ G β K
  have hc' := congrArg (fun z => G.mapDerivedCategory.map
      (R₁.mapDerivedCategoryFactors.hom.app K) ≫ z ≫
        R₂.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K)) (hc K)
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Functor.map_id, Category.id_comp, Iso.inv_hom_id_app] at hc'
  have hi := Category.comp_id (DerivedCategory.Q.map
    ((β.hom.mapHomologicalComplex (.up ℤ)).app K))
  have hc'' := hc'.trans (congrArg (fun z =>
    G.mapDerivedCategory.map (R₁.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((R₁.mapHomologicalComplex (.up ℤ)).obj K) ≫ z) hi)
  apply (cancel_mono (R₂.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
    R₂.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K))).mp
  simpa only [Category.assoc] using hc''.trans hf

end CategoryTheory
