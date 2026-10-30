/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.OriginalSections.Pullback
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ExactFunctor
public import Aglib.CategoryTheory.Abelian.Injective.ExactFunctorPlus

/-! # Original derived section pullback and actual resolution maps

The actual ordinary adjunction and right-section comparison construct all maps.
Preservation of injectives by the right adjoint is derived from the left adjoint's
monomorphism preservation. No injectivity preservation is assumed of the left
functor or coefficient forgetting. Each of the three actual categories retains
its own independent derived realization.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory.Adjunction

universe uC vC dC uD vD dD uV vV dV

variable {C : Type uC} [Category.{vC} C] [Abelian C] [EnoughInjectives C]
  [HasDerivedCategory.{dC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [EnoughInjectives D]
  [HasDerivedCategory.{dD} D]
  {V : Type uV} [Category.{vV} V] [Abelian V] [HasDerivedCategory.{dV} V]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (adj : F ⊣ G) (Γ : C ⥤ V) {Δ : D ⥤ V} [Γ.Additive] [Δ.Additive]
  (e : G ⋙ Γ ≅ Δ)

/-- Actual derived direct image followed by actual derived sections is derived
sections on the source, using preservation of injectives by direct image only. -/
def derivedRightSectionsIso :
    G.rightDerivedFunctorPlus ⋙ Γ.rightDerivedFunctorPlus ≅ Δ.rightDerivedFunctorPlus := by
  letI : G.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  exact (Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives G Γ).symm ≪≫
    (G ⋙ Γ).rightDerivedFunctorPlusIso e

/-- The canonical D+ map on global sections, constructed from the actual
inverse-image/direct-image derived adjunction unit. -/
def derivedUnitSectionsPullback (K : DerivedCategory.Plus C) :
    (Γ.rightDerivedFunctorPlus).obj K ⟶
      (Δ.rightDerivedFunctorPlus).obj (F.rightDerivedFunctorPlus.obj K) :=
  (Γ.rightDerivedFunctorPlus).map (adj.rightDerivedFunctorPlus.unit.app K) ≫
    (derivedRightSectionsIso adj Γ e).hom.app (F.rightDerivedFunctorPlus.obj K)

/-- The canonical derived map on coefficient singles, with the original
exact-single comparison on the target. -/
def derivedUnitSectionsPullbackSingle (L : C) :
    (Γ.rightDerivedFunctorPlus).obj
        ((DerivedCategory.Plus.singleFunctor C 0).obj L) ⟶
      (Δ.rightDerivedFunctorPlus).obj
        ((DerivedCategory.Plus.singleFunctor D 0).obj
          (F.obj L)) :=
  derivedUnitSectionsPullback adj Γ e
      ((DerivedCategory.Plus.singleFunctor C 0).obj L) ≫
    (Δ.rightDerivedFunctorPlus).map
      ((F.rightDerivedFunctorPlusSingleIso 0).hom.app L)

/-- The higher-sections map obtained from homology of the actual canonical D+
map, retaining the native single/homology isomorphisms. -/
def rightDerivedUnitSectionsPullback (L : C) (n : ℕ) :
    (Γ.rightDerived n).obj L ⟶
      (Δ.rightDerived n).obj (F.obj L) :=
  (Γ.rightDerivedSingleHomologyIso n).hom.app L ≫
    (DerivedCategory.Plus.homologyFunctor V (n : ℤ)).map
      (derivedUnitSectionsPullbackSingle adj Γ e L) ≫
    (Δ.rightDerivedSingleHomologyIso n).inv.app (F.obj L)


/-- The direct-image/sections comparison retains both original derived units. -/
@[reassoc]
theorem derivedRightSectionsIso_unit (K : CochainComplex.Plus D) :
    Γ.rightDerivedFunctorPlusUnit.app
        (G.mapCochainComplexPlus.obj K) ≫
      (Γ.rightDerivedFunctorPlus).map (G.rightDerivedFunctorPlusUnit.app K) ≫
      (derivedRightSectionsIso adj Γ e).hom.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus e).hom.app K) ≫
      Δ.rightDerivedFunctorPlusUnit.app K := by
  let : G.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  let c := Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives
    G Γ
  let t := (G ⋙ Γ).rightDerivedFunctorPlusIso e
  have hc := Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app
    G Γ K
  change _ ≫ _ ≫ (c.inv.app _ ≫ t.hom.app _) = _
  rw [← Category.assoc, ← hc]
  simp only [Category.assoc]
  change (G ⋙ Γ).rightDerivedFunctorPlusUnit.app K ≫
    c.hom.app (DerivedCategory.Plus.Q.obj K) ≫
      c.inv.app (DerivedCategory.Plus.Q.obj K) ≫ t.hom.app (DerivedCategory.Plus.Q.obj K) = _
  rw [Iso.hom_inv_id_app_assoc]
  exact (G ⋙ Γ).rightDerivedFunctorPlusIso_hom_app
    e K

omit [HasDerivedCategory.{dC} C] [HasDerivedCategory.{dD} D]
  [HasDerivedCategory.{dV} V] [EnoughInjectives C] [EnoughInjectives D]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- The ordinary section-complex map defined by the original adjunction unit. -/
def unitSectionsPullbackComplex (K : CochainComplex.Plus C) :
    Γ.mapCochainComplexPlus.obj K ⟶
      Δ.mapCochainComplexPlus.obj
        (F.mapCochainComplexPlus.obj K) :=
  Γ.mapCochainComplexPlus.map
      (adj.mapCochainComplexPlus.unit.app K) ≫
    (NatIso.mapCochainComplexPlus e).hom.app
      (F.mapCochainComplexPlus.obj K)

omit [HasDerivedCategory.{dC} C] [HasDerivedCategory.{dD} D]
  [HasDerivedCategory.{dV} V] [EnoughInjectives C] [EnoughInjectives D]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- Each component is the old ordinary section pullback, not a new map. -/
theorem unitSectionsPullbackComplex_f (K : CochainComplex.Plus C) (i : ℤ) :
    (unitSectionsPullbackComplex adj Γ e K).hom.f i =
      (unitSectionsNatTrans adj Γ e).app (K.obj.X i) := rfl

/-- Coefficient naturality of the actual canonical D+ sections map. -/
@[reassoc]
theorem derivedUnitSectionsPullback_naturality {K L : DerivedCategory.Plus C} (q : K ⟶ L) :
    (Γ.rightDerivedFunctorPlus).map q ≫ derivedUnitSectionsPullback adj Γ e L =
      derivedUnitSectionsPullback adj Γ e K ≫
        (Δ.rightDerivedFunctorPlus).map (F.rightDerivedFunctorPlus.map q) := by
  have hη := adj.rightDerivedFunctorPlus.unit.naturality q
  change q ≫ adj.rightDerivedFunctorPlus.unit.app L =
    adj.rightDerivedFunctorPlus.unit.app K ≫
      G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlus.map q) at hη
  have he := (derivedRightSectionsIso adj Γ e).hom.naturality
    (F.rightDerivedFunctorPlus.map q)
  change (Γ.rightDerivedFunctorPlus).map (G.rightDerivedFunctorPlus.map
      (F.rightDerivedFunctorPlus.map q)) ≫
        (derivedRightSectionsIso adj Γ e).hom.app (F.rightDerivedFunctorPlus.obj L) =
    (derivedRightSectionsIso adj Γ e).hom.app (F.rightDerivedFunctorPlus.obj K) ≫
      (Δ.rightDerivedFunctorPlus).map (F.rightDerivedFunctorPlus.map q) at he
  dsimp only [derivedUnitSectionsPullback]
  rw [← CategoryTheory.Functor.map_comp_assoc, hη, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [he]

/-- The canonical D+ map retains the original section map and localization units
on every bounded-below complex. No inverse-image injectivity is assumed. -/
@[reassoc]
theorem derivedUnitSectionsPullback_unit (K : CochainComplex.Plus C) :
    Γ.rightDerivedFunctorPlusUnit.app K ≫
      derivedUnitSectionsPullback adj Γ e (DerivedCategory.Plus.Q.obj K) ≫
      (Δ.rightDerivedFunctorPlus).map
        (F.rightDerivedFunctorPlusExactComparison.hom.app K) =
    DerivedCategory.Plus.Q.map (unitSectionsPullbackComplex adj Γ e K) ≫
      Δ.rightDerivedFunctorPlusUnit.app
        (F.mapCochainComplexPlus.obj K) := by
  let l := F.rightDerivedFunctorPlusExactComparison.hom.app K
  have hc := (derivedRightSectionsIso adj Γ e).hom.naturality l
  change (Γ.rightDerivedFunctorPlus).map (G.rightDerivedFunctorPlus.map l) ≫
      (derivedRightSectionsIso adj Γ e).hom.app
        (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K)) =
    (derivedRightSectionsIso adj Γ e).hom.app
      (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≫
        (Δ.rightDerivedFunctorPlus).map l at hc
  dsimp only [l] at hc
  have hu := adj.rightDerivedFunctorPlus_unit_fac K
  have hA := Γ.rightDerivedFunctorPlusUnit.naturality
    (adj.mapCochainComplexPlus.unit.app K)
  change DerivedCategory.Plus.Q.map (Γ.mapCochainComplexPlus.map
      (adj.mapCochainComplexPlus.unit.app K)) ≫
        Γ.rightDerivedFunctorPlusUnit.app
          (G.mapCochainComplexPlus.obj
            (F.mapCochainComplexPlus.obj K)) =
    Γ.rightDerivedFunctorPlusUnit.app K ≫
      (Γ.rightDerivedFunctorPlus).map
        (DerivedCategory.Plus.Q.map
          (adj.mapCochainComplexPlus.unit.app K)) at hA
  dsimp only [derivedUnitSectionsPullback]
  simp only [Category.assoc]
  rw [← hc, ← CategoryTheory.Functor.map_comp_assoc, hu, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hA]
  rw [derivedRightSectionsIso_unit]
  simp only [unitSectionsPullbackComplex, CategoryTheory.Functor.map_comp, Category.assoc]

omit [HasDerivedCategory.{dC} C] [HasDerivedCategory.{dD} D]
  [HasDerivedCategory.{dV} V] [EnoughInjectives C] [EnoughInjectives D]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- The compatible lift from the exact image of the source resolution, bundled
in the original bounded-below category. -/
def resolutionLiftPlus {L : C} (I : InjectiveResolution L)
    (J : InjectiveResolution (F.obj L))
    (φ : InjectiveResolution.ExactFunctor.mappedResolution F I ⟶
      J.cocomplex) :
    F.mapCochainComplexPlus.obj I.cochainComplexPlus ⟶
      J.cochainComplexPlus :=
  ObjectProperty.homMk
    (InjectiveResolution.ExactFunctor.extendedLift F I J φ)

omit [HasDerivedCategory.{dC} C] [HasDerivedCategory.{dD} D]
  [HasDerivedCategory.{dV} V] [EnoughInjectives C] [EnoughInjectives D]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- The lifted augmentation agrees with the original native exact-single map. -/
theorem resolutionLiftPlus_augmentation {L : C} (I : InjectiveResolution L)
    (J : InjectiveResolution (F.obj L))
    (φ : InjectiveResolution.ExactFunctor.mappedResolution F I ⟶
      J.cocomplex)
    (hφ : F.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    F.mapCochainComplexPlus.map I.ιPlus ≫
        resolutionLiftPlus (F := F) I J φ =
      (show F.mapCochainComplexPlus.obj
          ((CochainComplex.singleFunctorPlus C 0).obj L) ⟶
          (CochainComplex.singleFunctorPlus D 0).obj
            (F.obj L) from
        ObjectProperty.homMk
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app L)) ≫
        J.ιPlus := by
  apply ObjectProperty.hom_ext
  change (F.mapHomologicalComplex (.up ℤ)).map I.ι' ≫
      InjectiveResolution.ExactFunctor.extendedLift F I J φ =
    (F.mapCochainComplexSingleFunctor 0).hom.app L ≫ J.ι'
  apply (cancel_epi ((F.mapCochainComplexSingleFunctor 0).inv.app L)).mp
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc] using
    InjectiveResolution.ExactFunctor.extendedLift_augmentation
      F I J (𝟙 _) φ (by simpa only [Category.id_comp] using hφ)

omit [HasDerivedCategory.{dV} V] [EnoughInjectives D] in
/-- The exact derived comparison carries the lifted resolution augmentation to
the same native exact-single map. -/
theorem resolutionLiftPlus_derived_augmentation {L : C} (I : InjectiveResolution L)
    (J : InjectiveResolution (F.obj L))
    (φ : InjectiveResolution.ExactFunctor.mappedResolution F I ⟶
      J.cocomplex)
    (hφ : F.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map I.ιPlus) ≫
        F.rightDerivedFunctorPlusExactComparison.hom.app I.cochainComplexPlus ≫
        DerivedCategory.Plus.Q.map (resolutionLiftPlus (F := F) I J φ) =
      (F.rightDerivedFunctorPlusSingleIso 0).hom.app L ≫
        DerivedCategory.Plus.Q.map J.ιPlus := by
  let K := (CochainComplex.singleFunctorPlus C 0).obj L
  let : IsIso F.rightDerivedFunctorPlusUnit :=
    F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have hn := F.rightDerivedFunctorPlusUnit.naturality I.ιPlus
  change DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map I.ιPlus) ≫
      F.rightDerivedFunctorPlusUnit.app I.cochainComplexPlus =
    F.rightDerivedFunctorPlusUnit.app K ≫
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map I.ιPlus) at hn
  apply (cancel_epi (F.rightDerivedFunctorPlusUnit.app K)).mp
  rw [← Category.assoc, ← hn]
  have hc : F.rightDerivedFunctorPlusUnit.app I.cochainComplexPlus ≫
      F.rightDerivedFunctorPlusExactComparison.hom.app I.cochainComplexPlus =
        𝟙 _ := by
    change (asIso F.rightDerivedFunctorPlusUnit).hom.app _ ≫
      (asIso F.rightDerivedFunctorPlusUnit).inv.app _ = 𝟙 _
    exact (asIso F.rightDerivedFunctorPlusUnit).hom_inv_id_app _
  simp only [Category.assoc]
  rw [← Category.assoc (F.rightDerivedFunctorPlusUnit.app I.cochainComplexPlus),
    hc, Category.id_comp]
  rw [← CategoryTheory.Functor.map_comp, resolutionLiftPlus_augmentation (F := F) I J φ hφ,
    CategoryTheory.Functor.map_comp]
  erw [← Category.assoc, Functor.rightDerivedFunctorPlusSingleIso_unit]

/-- The canonical D+ sections map equals the independently constructed section
map on supplied resolutions, before taking homology. -/
theorem derivedUnitSectionsPullbackSingle_resolution {L : C} (I : InjectiveResolution L)
    (J : InjectiveResolution (F.obj L))
    (φ : InjectiveResolution.ExactFunctor.mappedResolution F I ⟶
      J.cocomplex)
    (hφ : F.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    (I.rightDerivedFunctorPlusIso Γ).hom ≫
        derivedUnitSectionsPullbackSingle adj Γ e L =
      DerivedCategory.Plus.Q.map
        (unitSectionsPullbackComplex adj Γ e I.cochainComplexPlus ≫
          Δ.mapCochainComplexPlus.map
            (resolutionLiftPlus (F := F) I J φ)) ≫
        (J.rightDerivedFunctorPlusIso Δ).hom := by
  apply (cancel_mono ((Δ.rightDerivedFunctorPlus).map
    (DerivedCategory.Plus.Q.map J.ιPlus))).mp
  simp only [derivedUnitSectionsPullbackSingle, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp,
    ← resolutionLiftPlus_derived_augmentation (F := F) I J φ hφ]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← derivedUnitSectionsPullback_naturality_assoc]
  rw [InjectiveResolution.rightDerivedFunctorPlusIso_hom_comp_assoc,
    derivedUnitSectionsPullback_unit_assoc]
  erw [← Δ.rightDerivedFunctorPlusUnit.naturality
    (resolutionLiftPlus (F := F) I J φ)]
  erw [InjectiveResolution.rightDerivedFunctorPlusIso_hom_comp]
  rfl


/-- Homology of the actual canonical D+ sections map is the independently
defined map of the original section-resolution complexes. -/
theorem rightDerivedUnitSectionsPullback_eq_resolution {L : C} (I : InjectiveResolution L)
    (J : InjectiveResolution (F.obj L))
    (φ : InjectiveResolution.ExactFunctor.mappedResolution F I ⟶
      J.cocomplex)
    (hφ : F.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) (n : ℕ) :
    rightDerivedUnitSectionsPullback adj Γ e L n =
      (I.isoRightDerivedObjCochain Γ n).hom ≫
        HomologicalComplex.homologyMap
          (unitSectionsPullbackComplex adj Γ e I.cochainComplexPlus ≫
            Δ.mapCochainComplexPlus.map
              (resolutionLiftPlus (F := F) I J φ)).hom (n : ℤ) ≫
        (J.isoRightDerivedObjCochain Δ n).inv := by
  let H := DerivedCategory.Plus.homologyFunctor V (n : ℤ)
  let ψ := unitSectionsPullbackComplex adj Γ e I.cochainComplexPlus ≫
    Δ.mapCochainComplexPlus.map (resolutionLiftPlus (F := F) I J φ)
  let pI := (DerivedCategory.Plus.homologyFunctorFactors
    (A := V) (n : ℤ)).app
      (Γ.mapCochainComplexPlus.obj I.cochainComplexPlus)
  let pJ := (DerivedCategory.Plus.homologyFunctorFactors
    (A := V) (n : ℤ)).app
      (Δ.mapCochainComplexPlus.obj J.cochainComplexPlus)
  have hP := (DerivedCategory.Plus.homologyFunctorFactors
    (A := V) (n : ℤ)).hom.naturality ψ
  change H.map (DerivedCategory.Plus.Q.map ψ) ≫ pJ.hom =
    pI.hom ≫ HomologicalComplex.homologyMap ψ.hom (n : ℤ) at hP
  have hP' : pI.inv ≫ H.map (DerivedCategory.Plus.Q.map ψ) =
      HomologicalComplex.homologyMap ψ.hom (n : ℤ) ≫ pJ.inv := by
    apply (cancel_mono pJ.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hP]
    simp only [Iso.inv_hom_id_assoc]
  have hD : H.map (I.rightDerivedFunctorPlusIso Γ).hom ≫
      H.map (derivedUnitSectionsPullbackSingle adj Γ e L) =
    H.map (DerivedCategory.Plus.Q.map ψ) ≫
      H.map (J.rightDerivedFunctorPlusIso Δ).hom := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg H.map (derivedUnitSectionsPullbackSingle_resolution adj Γ e I J φ hφ)
  have hs :
      (I.isoRightDerivedSingleHomology Γ n).hom ≫
          H.map (derivedUnitSectionsPullbackSingle adj Γ e L) =
        ((I.isoRightDerivedObjCochain Γ n).hom ≫
          HomologicalComplex.homologyMap ψ.hom (n : ℤ) ≫
          (J.isoRightDerivedObjCochain Δ n).inv) ≫
            (J.isoRightDerivedSingleHomology Δ n).hom := by
    simp only [InjectiveResolution.isoRightDerivedSingleHomology_hom, Category.assoc]
    rw [hD]
    change (I.isoRightDerivedObjCochain Γ n).hom ≫
        pI.inv ≫ H.map (DerivedCategory.Plus.Q.map ψ) ≫
          H.map (J.rightDerivedFunctorPlusIso Δ).hom = _
    rw [← Category.assoc pI.inv, hP']
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  apply (cancel_mono
    ((Δ.rightDerivedSingleHomologyIso n).hom.app
      (F.obj L))).mp
  simp only [rightDerivedUnitSectionsPullback, Category.assoc, Iso.inv_hom_id_app]
  rw [Γ.rightDerivedSingleHomologyIso_hom_app I n,
    Δ.rightDerivedSingleHomologyIso_hom_app J n]
  simp only [Category.assoc] at hs
  exact (congrArg (fun k => (I.isoRightDerivedSingleHomology Γ n).hom ≫ k)
    (Category.comp_id (H.map (derivedUnitSectionsPullbackSingle adj Γ e L)))).trans hs


end CategoryTheory.Adjunction
