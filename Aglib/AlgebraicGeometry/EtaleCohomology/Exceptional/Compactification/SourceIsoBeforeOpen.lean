/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.Pasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.SourceIsoPasting

/-! # Original source transport before an open Cartesian exchange -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX₀ wX₁ wX₂ wM₀ wM₂
variable {X₀ X₁ X₂ M₀ M₂ : Scheme.{u}}
  (j₀ : X₀ ⟶ M₀) (e : X₁ ≅ X₀) (j₂ : X₂ ⟶ M₂)
  (a : X₂ ⟶ X₁) (q : M₂ ⟶ M₀)
  [IsOpenImmersion j₀] [IsOpenImmersion j₂]
  (hj : IsPullback a j₂ (e.hom ≫ j₀) q)
  (ht : IsPullback (a ≫ e.hom) j₂ j₀ q)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX₀} (ModuleSheaf X₀ Λ)]
  [HasDerivedCategory.{wX₁} (ModuleSheaf X₁ Λ)]
  [HasDerivedCategory.{wX₂} (ModuleSheaf X₂ Λ)]
  [HasDerivedCategory.{wM₀} (ModuleSheaf M₀ Λ)]
  [HasDerivedCategory.{wM₂} (ModuleSheaf M₂ Λ)]

omit [HasDerivedCategory.{wX₁} (ModuleSheaf X₁ Λ)] in
private theorem source_before_open_total_transport
    (ht' : IsPullback (a ≫ e.hom) j₂ j₀ (q ≫ 𝟙 M₀))
    (K : DerivedCategory.Plus (ModuleSheaf X₀ Λ)) :
    (eqToIso (congrArg (fun z => moduleDerivedInverseImage Λ z)
      (Category.comp_id q))).hom.app ((moduleDerivedLowerShriek j₀ Λ).obj K) ≫
        (moduleDerivedLowerShriekCartesianBaseChangeIso (a ≫ e.hom) j₂ j₀ q ht Λ).hom.app K =
      (moduleDerivedLowerShriekCartesianBaseChangeIso
        (a ≫ e.hom) j₂ j₀ (q ≫ 𝟙 M₀) ht' Λ).hom.app K := by
  have h : ∀ (q₀ q₁ : M₂ ⟶ M₀) (hq : q₀ = q₁)
      (h₀ : IsPullback (a ≫ e.hom) j₂ j₀ q₀)
      (h₁ : IsPullback (a ≫ e.hom) j₂ j₀ q₁),
      (eqToIso (congrArg (fun z => moduleDerivedInverseImage Λ z) hq)).hom.app
          ((moduleDerivedLowerShriek j₀ Λ).obj K) ≫
        (moduleDerivedLowerShriekCartesianBaseChangeIso (a ≫ e.hom) j₂ j₀ q₁ h₁ Λ).hom.app K =
      (moduleDerivedLowerShriekCartesianBaseChangeIso (a ≫ e.hom) j₂ j₀ q₀ h₀ Λ).hom.app K := by
    intro q₀ q₁ hq h₀ h₁
    subst q₁
    simp
  exact h _ _ (Category.comp_id q) ht' ht

/-- Source transport followed by the original open exchange is the original
composite-source exchange, with its original inverse-image compositor. -/
theorem moduleDerivedOpenComparison_sourceIso_before
    (K : DerivedCategory.Plus (ModuleSheaf X₀ Λ)) :
    (moduleDerivedInverseImage Λ q).map
        ((moduleDerivedLowerShriekSourceIso e j₀ Λ).hom.app K) ≫
      (moduleDerivedLowerShriekCartesianBaseChangeIso a j₂ (e.hom ≫ j₀) q hj Λ).hom.app
        ((moduleDerivedInverseImage Λ e.hom).obj K) =
      (moduleDerivedLowerShriekCartesianBaseChangeIso (a ≫ e.hom) j₂ j₀ q ht Λ).hom.app K ≫
        (moduleDerivedLowerShriek j₂ Λ).map
          ((moduleDerivedInverseImageCompIso Λ e.hom a).hom.app K) := by
  let ht' := hj.paste_horiz (isPullback_sourceIsoOpen e j₀)
  apply source_before_open_from_pasting (moduleDerivedInverseImage Λ q)
    (moduleDerivedInverseImageIdIso Λ M₀)
    ((moduleDerivedLowerShriekCartesianBaseChangeIso e.hom (e.hom ≫ j₀) j₀ (𝟙 M₀)
      (isPullback_sourceIsoOpen e j₀) Λ).hom.app K)
    ((moduleDerivedLowerShriekSourceIso e j₀ Λ).hom.app K)
    ((moduleDerivedLowerShriekCartesianBaseChangeIso a j₂ (e.hom ≫ j₀) q hj Λ).hom.app
      ((moduleDerivedInverseImage Λ e.hom).obj K))
    ((moduleDerivedInverseImageCompIso Λ (𝟙 M₀) q).hom.app
      ((moduleDerivedLowerShriek j₀ Λ).obj K))
    ((eqToIso (congrArg (fun z => moduleDerivedInverseImage Λ z)
      (Category.comp_id q))).app ((moduleDerivedLowerShriek j₀ Λ).obj K)) _ _
  · simp only [moduleDerivedLowerShriekSourceIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.rightUnitor_inv_app, Category.id_comp]
  · exact source_before_open_unit_component _ _ _
      (moduleDerivedInverseImageCompIso_id_comp Λ q) _
  · exact moduleDerivedOpenComparison_pasting j₀ (e.hom ≫ j₀) j₂ e.hom a
      (𝟙 M₀) q (isPullback_sourceIsoOpen e j₀) hj ht' Λ K
  · exact (reassoc_of% (source_before_open_total_transport j₀ e j₂ a q ht Λ ht' K))
      ((moduleDerivedLowerShriek j₂ Λ).map
        ((moduleDerivedInverseImageCompIso Λ e.hom a).hom.app K))

end AlgebraicGeometry.Scheme.EtaleCohomology
