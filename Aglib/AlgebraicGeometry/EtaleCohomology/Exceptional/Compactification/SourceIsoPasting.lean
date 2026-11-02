/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.Pasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.SourceIsoExchange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenComparisonCube
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.InverseImageIdentityCoherence

/-! # Original base change followed by actual source-isomorphism transport -/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wU₀ wU₁ wU₂ wM₀ wM₁

variable {U₀ U₁ U₂ M₀ M₁ : Scheme.{u}}
  (j₀ : U₀ ⟶ M₀) (j₁ : U₁ ⟶ M₁) (a : U₁ ⟶ U₀) (q : M₁ ⟶ M₀)
  [IsOpenImmersion j₀] [IsOpenImmersion j₁] (e : U₂ ≅ U₁)
  (hj : IsPullback a j₁ j₀ q)
  (hj' : IsPullback (e.hom ≫ a) (e.hom ≫ j₁) j₀ q)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wU₀} (ModuleSheaf U₀ Λ)]
  [HasDerivedCategory.{wU₁} (ModuleSheaf U₁ Λ)]
  [HasDerivedCategory.{wU₂} (ModuleSheaf U₂ Λ)]
  [HasDerivedCategory.{wM₀} (ModuleSheaf M₀ Λ)]
  [HasDerivedCategory.{wM₁} (ModuleSheaf M₁ Λ)]

private theorem sourceIso_lowerShriek_app (M : DerivedCategory.Plus (ModuleSheaf U₁ Λ)) :
    (moduleDerivedLowerShriekSourceIso e j₁ Λ).hom.app M =
      (moduleDerivedInverseImageIdIso Λ M₁).inv.app ((moduleDerivedLowerShriek j₁ Λ).obj M) ≫
        (moduleDerivedLowerShriekCartesianBaseChangeIso e.hom (e.hom ≫ j₁) j₁ (𝟙 M₁)
          (isPullback_sourceIsoOpen e j₁) Λ).hom.app M := by
  simp only [moduleDerivedLowerShriekSourceIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.rightUnitor_inv_app, Category.id_comp, Functor.comp_obj, Functor.id_obj]

private theorem sourceIso_ambientComp_app (K : DerivedCategory.Plus (ModuleSheaf U₀ Λ)) :
    (moduleDerivedInverseImageCompIso Λ q (𝟙 M₁)).hom.app
        ((moduleDerivedLowerShriek j₀ Λ).obj K) ≫
      (moduleDerivedInverseImageIdIso Λ M₁).hom.app
        ((moduleDerivedInverseImage Λ q).obj ((moduleDerivedLowerShriek j₀ Λ).obj K)) =
    (eqToIso (congrArg (fun t => moduleDerivedInverseImage Λ t) (Category.id_comp q))).hom.app
      ((moduleDerivedLowerShriek j₀ Λ).obj K) := by
  simpa only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.comp_obj,
    Functor.id_obj, Category.comp_id] using congrArg
      (fun t => t.hom.app ((moduleDerivedLowerShriek j₀ Λ).obj K))
      (moduleDerivedInverseImageCompIso_comp_id Λ q)

omit [HasDerivedCategory.{wU₁} (ModuleSheaf U₁ Λ)] in
private theorem sourceIso_open_total_transport
    (ht : IsPullback (e.hom ≫ a) (e.hom ≫ j₁) j₀ (𝟙 M₁ ≫ q))
    (K : DerivedCategory.Plus (ModuleSheaf U₀ Λ)) :
    (eqToIso (congrArg (fun t => moduleDerivedInverseImage Λ t) (Category.id_comp q))).hom.app
        ((moduleDerivedLowerShriek j₀ Λ).obj K) ≫
      (moduleDerivedLowerShriekCartesianBaseChangeIso
        (e.hom ≫ a) (e.hom ≫ j₁) j₀ q hj' Λ).hom.app K =
    (moduleDerivedLowerShriekCartesianBaseChangeIso
      (e.hom ≫ a) (e.hom ≫ j₁) j₀ (𝟙 M₁ ≫ q) ht Λ).hom.app K := by
  have he : ∀ (q₀ q₁ : M₁ ⟶ M₀) (hq : q₀ = q₁)
      (h₀ : IsPullback (e.hom ≫ a) (e.hom ≫ j₁) j₀ q₀)
      (h₁ : IsPullback (e.hom ≫ a) (e.hom ≫ j₁) j₀ q₁),
      (eqToIso (congrArg (fun t => moduleDerivedInverseImage Λ t) hq)).hom.app
          ((moduleDerivedLowerShriek j₀ Λ).obj K) ≫
        (moduleDerivedLowerShriekCartesianBaseChangeIso
          (e.hom ≫ a) (e.hom ≫ j₁) j₀ q₁ h₁ Λ).hom.app K =
      (moduleDerivedLowerShriekCartesianBaseChangeIso
        (e.hom ≫ a) (e.hom ≫ j₁) j₀ q₀ h₀ Λ).hom.app K := by
    intro q₀ q₁ hq h₀ h₁
    subst q₁
    simp
  exact he _ _ (Category.id_comp q) ht hj'

/-- Original open base change followed by the actual source isomorphism has
exactly the original source inverse-image composition comparison. -/
theorem moduleDerivedOpenComparison_sourceIso_pasting :
    OpenSourceIsoPastingEquation
      (moduleDerivedLowerShriekCartesianBaseChangeIso a j₁ j₀ q hj Λ)
      (moduleDerivedLowerShriekCartesianBaseChangeIso
        (e.hom ≫ a) (e.hom ≫ j₁) j₀ q hj' Λ)
      (moduleDerivedLowerShriekSourceIso e j₁ Λ)
      (moduleDerivedInverseImageCompIso Λ a e.hom) := by
  intro K
  let ht := (isPullback_sourceIsoOpen e j₁).paste_horiz hj
  apply source_transport_from_identity_pasting (moduleDerivedInverseImageIdIso Λ M₁)
    ((moduleDerivedLowerShriekCartesianBaseChangeIso a j₁ j₀ q hj Λ).hom.app K)
    ((moduleDerivedLowerShriekCartesianBaseChangeIso e.hom (e.hom ≫ j₁) j₁ (𝟙 M₁)
      (isPullback_sourceIsoOpen e j₁) Λ).hom.app ((moduleDerivedInverseImage Λ a).obj K))
    ((moduleDerivedLowerShriekSourceIso e j₁ Λ).hom.app ((moduleDerivedInverseImage Λ a).obj K))
    ((moduleDerivedInverseImageCompIso Λ q (𝟙 M₁)).hom.app
      ((moduleDerivedLowerShriek j₀ Λ).obj K))
    ((eqToIso (congrArg (fun t => moduleDerivedInverseImage Λ t)
      (Category.id_comp q))).app ((moduleDerivedLowerShriek j₀ Λ).obj K))
    ((moduleDerivedLowerShriekCartesianBaseChangeIso
      (e.hom ≫ a) (e.hom ≫ j₁) j₀ (𝟙 M₁ ≫ q) ht Λ).hom.app K ≫
      (moduleDerivedLowerShriek (e.hom ≫ j₁) Λ).map
        ((moduleDerivedInverseImageCompIso Λ a e.hom).hom.app K))
  · exact sourceIso_lowerShriek_app j₁ e Λ ((moduleDerivedInverseImage Λ a).obj K)
  · exact sourceIso_ambientComp_app j₀ q Λ K
  · exact moduleDerivedOpenComparison_pasting j₀ j₁ (e.hom ≫ j₁) a e.hom q (𝟙 M₁)
      hj (isPullback_sourceIsoOpen e j₁) ht Λ K
  · exact (reassoc_of% (sourceIso_open_total_transport j₀ j₁ a q e hj' Λ ht K))
      ((moduleDerivedLowerShriek (e.hom ≫ j₁) Λ).map
        ((moduleDerivedInverseImageCompIso Λ a e.hom).hom.app K))

end AlgebraicGeometry.Scheme.EtaleCohomology
