/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.OpenRefinementNormalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenComparisonCube
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenBaseChangeIdentity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.InverseImageIdentityCoherence

/-! # Original open/refinement cube through identity-normalized pasting -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

section ComponentNormalizations

universe wU wV wC wD

variable (Λ : Type (u + 1)) [Ring Λ]

private theorem inverseImageComp_first_identity_app {U V : Scheme.{u}} (a : V ⟶ U)
    [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
    [HasDerivedCategory.{wV} (ModuleSheaf V Λ)]
    (K : DerivedCategory.Plus (ModuleSheaf U Λ)) :
    (moduleDerivedInverseImageCompIso Λ (𝟙 U) a).hom.app K ≫
      (moduleDerivedInverseImage Λ a).map ((moduleDerivedInverseImageIdIso Λ U).hom.app K) =
      (eqToIso (congrArg (fun f => moduleDerivedInverseImage Λ f)
        (Category.comp_id a))).hom.app K := by
  simpa only [Iso.trans_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Category.comp_id,
    eqToIso.hom, eqToHom_app, eqToHom_refl, NatTrans.id_app,
    Functor.comp_obj, Functor.id_obj] using
    congrArg (fun e => e.hom.app K) (moduleDerivedInverseImageCompIso_id_comp Λ a)

private theorem inverseImageComp_second_identity_app {U V : Scheme.{u}} (a : V ⟶ U)
    [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
    [HasDerivedCategory.{wV} (ModuleSheaf V Λ)]
    (K : DerivedCategory.Plus (ModuleSheaf U Λ)) :
    (moduleDerivedInverseImageCompIso Λ a (𝟙 V)).hom.app K ≫
      (moduleDerivedInverseImageIdIso Λ V).hom.app ((moduleDerivedInverseImage Λ a).obj K) =
      (eqToIso (congrArg (fun f => moduleDerivedInverseImage Λ f)
        (Category.id_comp a))).hom.app K := by
  simpa only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Category.comp_id, Category.id_comp,
    eqToIso.hom, eqToHom_app, eqToHom_refl, NatTrans.id_app,
    Functor.comp_obj, Functor.id_obj] using
    congrArg (fun e => e.hom.app K) (moduleDerivedInverseImageCompIso_comp_id Λ a)

private theorem properRefinementPullback_normalization_app
    {U C D : Scheme.{u}} (jC : U ⟶ C) (jD : U ⟶ D) (h : C ⟶ D)
    [IsOpenImmersion jC] [IsOpenImmersion jD] (sq : IsPullback jC (𝟙 U) h jD)
    [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
    [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]
    [HasDerivedCategory.{wD} (ModuleSheaf D Λ)]
    (K : DerivedCategory.Plus (ModuleSheaf U Λ)) :
    (moduleDerivedProperRefinementPullbackIso jC jD h sq Λ).hom.app K =
      (moduleDerivedLowerShriekCartesianBaseChangeIso (𝟙 U) jC jD h sq.flip Λ).hom.app K ≫
        (moduleDerivedLowerShriek jC Λ).map ((moduleDerivedInverseImageIdIso Λ U).hom.app K) := by
  have hn := congrArg (fun e => e.hom.app K)
    (moduleDerivedLowerShriekCartesianBaseChangeIso_identity_source jC jD h sq.flip Λ)
  simpa only [moduleDerivedProperRefinementPullbackIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    Category.comp_id] using hn.symm

end ComponentNormalizations

section SourceTransport

universe wV wU wY wX

private theorem openComparison_congr_source_app
    {V U Y X : Scheme.{u}} (g₀ g₁ : V ⟶ U) (hg : g₀ = g₁)
    (i : V ⟶ Y) (j : U ⟶ X) (f : Y ⟶ X) [Etale i] [Etale j]
    (h₀ : IsPullback g₀ i j f) (h₁ : IsPullback g₁ i j f)
    (Λ : Type (u + 1)) [Ring Λ]
    [HasDerivedCategory.{wV} (ModuleSheaf V Λ)]
    [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
    [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    (K : DerivedCategory.Plus (ModuleSheaf U Λ)) :
    (moduleDerivedLowerShriekCartesianBaseChangeIso g₀ i j f h₀ Λ).hom.app K ≫
        (moduleDerivedLowerShriek i Λ).map
          ((eqToIso (congrArg (fun g => moduleDerivedInverseImage Λ g) hg)).hom.app K) =
      (moduleDerivedLowerShriekCartesianBaseChangeIso g₁ i j f h₁ Λ).hom.app K := by
  subst g₁
  simp

end SourceTransport

section NormalizedPasting

universe wU wU' wC wD wC'

variable {U U' C D C' : Scheme.{u}}
  (jC : U ⟶ C) (jD : U ⟶ D) (h : C ⟶ D)
  [IsOpenImmersion jC] [IsOpenImmersion jD] (sq : IsPullback jC (𝟙 U) h jD)
  (jC' : U' ⟶ C') [IsOpenImmersion jC'] (a : U' ⟶ U) (qC : C' ⟶ C)
  (hC : IsPullback a jC' jC qC) (ht : IsPullback a jC' jD (qC ≫ h))
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wU'} (ModuleSheaf U' Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D Λ)]
  [HasDerivedCategory.{wC'} (ModuleSheaf C' Λ)]

private theorem openComparison_pasting_first_identity :
    LeftFirstPastingEquation (moduleDerivedInverseImageCompIso Λ h qC)
      (moduleDerivedProperRefinementPullbackIso jC jD h sq Λ)
      (moduleDerivedLowerShriekCartesianBaseChangeIso a jC' jC qC hC Λ)
      (moduleDerivedLowerShriekCartesianBaseChangeIso a jC' jD (qC ≫ h) ht Λ) := by
  intro K
  let ht₀ := hC.paste_horiz sq.flip
  rw [← openComparison_congr_source_app (a ≫ 𝟙 U) a (Category.comp_id a)
    jC' jD (qC ≫ h) ht₀ ht Λ K]
  apply normalize_leftComparison_pasting_first
    (moduleDerivedInverseImageIdIso Λ U)
    (moduleDerivedLowerShriekCartesianBaseChangeIso (𝟙 U) jC jD h sq.flip Λ)
    (moduleDerivedProperRefinementPullbackIso jC jD h sq Λ)
    (moduleDerivedLowerShriekCartesianBaseChangeIso a jC' jC qC hC Λ) K
    (g := (moduleDerivedInverseImageCompIso Λ (𝟙 U) a).hom.app K)
  · exact properRefinementPullback_normalization_app Λ jC jD h sq K
  · exact inverseImageComp_first_identity_app Λ a K
  · exact moduleDerivedOpenComparison_pasting jD jC jC' (𝟙 U) a h qC sq.flip hC ht₀ Λ K

end NormalizedPasting

section NormalizedPastingSecond

universe wU wU' wD wD' wC'

variable {U U' D D' C' : Scheme.{u}}
  (jD : U ⟶ D) (jD' : U' ⟶ D') (jC' : U' ⟶ C') (h' : C' ⟶ D')
  [IsOpenImmersion jD] [IsOpenImmersion jD'] [IsOpenImmersion jC']
  (sq' : IsPullback jC' (𝟙 U') h' jD') (a : U' ⟶ U) (qD : D' ⟶ D)
  (hD : IsPullback a jD' jD qD) (ht : IsPullback a jC' jD (h' ≫ qD))
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wU'} (ModuleSheaf U' Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D Λ)]
  [HasDerivedCategory.{wD'} (ModuleSheaf D' Λ)]
  [HasDerivedCategory.{wC'} (ModuleSheaf C' Λ)]

private theorem openComparison_pasting_second_identity :
    LeftSecondPastingEquation (moduleDerivedInverseImageCompIso Λ qD h')
      (moduleDerivedLowerShriekCartesianBaseChangeIso a jD' jD qD hD Λ)
      (moduleDerivedProperRefinementPullbackIso jC' jD' h' sq' Λ)
      (moduleDerivedLowerShriekCartesianBaseChangeIso a jC' jD (h' ≫ qD) ht Λ) := by
  intro K
  let ht₀ := sq'.flip.paste_horiz hD
  rw [← openComparison_congr_source_app (𝟙 U' ≫ a) a (Category.id_comp a)
    jC' jD (h' ≫ qD) ht₀ ht Λ K, ← Category.assoc]
  apply normalize_leftComparison_pasting_second (moduleDerivedInverseImageIdIso Λ U')
    (moduleDerivedLowerShriekCartesianBaseChangeIso (𝟙 U') jC' jD' h' sq'.flip Λ)
    (moduleDerivedProperRefinementPullbackIso jC' jD' h' sq' Λ)
    ((moduleDerivedInverseImage Λ a).obj K)
    (g := (moduleDerivedInverseImageCompIso Λ a (𝟙 U')).hom.app K)
  · exact properRefinementPullback_normalization_app Λ jC' jD' h' sq'
      ((moduleDerivedInverseImage Λ a).obj K)
  · exact inverseImageComp_second_identity_app Λ a K
  · simpa only [Category.assoc] using
      moduleDerivedOpenComparison_pasting jD jD' jC' a (𝟙 U') qD h' hD sq'.flip ht₀ Λ K

end NormalizedPastingSecond

section TotalTransport

universe wV wU wY wX

private theorem openComparison_congr_left_app
    {V U Y X : Scheme.{u}} (g : V ⟶ U) (i : V ⟶ Y) (j : U ⟶ X)
    [Etale i] [Etale j] (f₀ f₁ : Y ⟶ X) (hf : f₀ = f₁)
    (h₀ : IsPullback g i j f₀) (h₁ : IsPullback g i j f₁)
    (Λ : Type (u + 1)) [Ring Λ]
    [HasDerivedCategory.{wV} (ModuleSheaf V Λ)]
    [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
    [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    : LeftTotalTransportEquation
      (eqToIso (congrArg (fun f => moduleDerivedInverseImage Λ f) hf))
      (moduleDerivedLowerShriekCartesianBaseChangeIso g i j f₁ h₁ Λ)
      (moduleDerivedLowerShriekCartesianBaseChangeIso g i j f₀ h₀ Λ) := by
  intro K
  subst f₁
  simp

end TotalTransport

section RefinementCube

universe wU wC wD wU' wC' wD'

variable {U C D U' C' D' : Scheme.{u}}
  (jC : U ⟶ C) (jD : U ⟶ D) (h : C ⟶ D)
  [IsOpenImmersion jC] [IsOpenImmersion jD] (sq : IsPullback jC (𝟙 U) h jD)
  (jC' : U' ⟶ C') (jD' : U' ⟶ D') (h' : C' ⟶ D')
  [IsOpenImmersion jC'] [IsOpenImmersion jD'] (sq' : IsPullback jC' (𝟙 U') h' jD')
  (a : U' ⟶ U) (qC : C' ⟶ C) (qD : D' ⟶ D)
  (hC : IsPullback a jC' jC qC) (hD : IsPullback a jD' jD qD)
  (hh : IsPullback qC h' h qD)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D Λ)]
  [HasDerivedCategory.{wU'} (ModuleSheaf U' Λ)]
  [HasDerivedCategory.{wC'} (ModuleSheaf C' Λ)]
  [HasDerivedCategory.{wD'} (ModuleSheaf D' Λ)]

/-- The actual Cartesian open/refinement cube commutes for the original maps.
No properness or torsion hypothesis is used by this equality. -/
theorem moduleDerivedOpenComparison_refinement_cube :
    LeftRefinementCubeEquation
      (moduleDerivedInverseImageSquareIso Λ h h' qD qC hh.w.symm)
      (moduleDerivedProperRefinementPullbackIso jC jD h sq Λ)
      (moduleDerivedProperRefinementPullbackIso jC' jD' h' sq' Λ)
      (moduleDerivedLowerShriekCartesianBaseChangeIso a jD' jD qD hD Λ)
      (moduleDerivedLowerShriekCartesianBaseChangeIso a jC' jC qC hC Λ) := by
  have ht₁ : IsPullback a jC' jD (qC ≫ h) := by
    simpa only [Category.comp_id] using hC.paste_horiz sq.flip
  have ht₂ : IsPullback a jC' jD (h' ≫ qD) := by
    simpa only [Category.id_comp] using sq'.flip.paste_horiz hD
  exact leftRefinementCube_of_pastings
    (moduleDerivedInverseImageSquareIso Λ h h' qD qC hh.w.symm)
    (moduleDerivedProperRefinementPullbackIso jC jD h sq Λ)
    (moduleDerivedProperRefinementPullbackIso jC' jD' h' sq' Λ)
    (moduleDerivedLowerShriekCartesianBaseChangeIso a jD' jD qD hD Λ)
    (moduleDerivedLowerShriekCartesianBaseChangeIso a jC' jC qC hC Λ)
    (moduleDerivedInverseImageCompIso Λ h qC)
    (moduleDerivedInverseImageCompIso Λ qD h')
    (eqToIso (congrArg (fun f => moduleDerivedInverseImage Λ f) hh.w.symm))
    (moduleDerivedLowerShriekCartesianBaseChangeIso a jC' jD (qC ≫ h) ht₁ Λ)
    (moduleDerivedLowerShriekCartesianBaseChangeIso a jC' jD (h' ≫ qD) ht₂ Λ) rfl
    (openComparison_pasting_first_identity jC jD h sq jC' a qC hC ht₁ Λ)
    (openComparison_pasting_second_identity jD jD' jC' h' sq' a qD hD ht₂ Λ)
    (openComparison_congr_left_app a jC' jD (h' ≫ qD) (qC ≫ h) hh.w.symm ht₂ ht₁ Λ)

end RefinementCube

end AlgebraicGeometry.Scheme.EtaleCohomology
