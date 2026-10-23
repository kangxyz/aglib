/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.Adjunction
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.CocycleComparison

/-!
# Identity and composition of original étale cohomological pullback

The comparisons are the existing inverse-image identity and composition
isomorphisms. The proofs retain their original constant-integer transport,
with no new choices of site or sheaf functors. Source, intermediate and target
Ext universes are independent.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w w' w''

attribute [local instance] hasSheafifyLarge

section Identity

variable (X : Scheme.{u}) [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Identity pullback is the identity after the native coefficient identification. -/
theorem cohomologyPullback_id (L : AbelianSheaf.{u, u + 1} X)
    (n : ℕ) (a : Sheaf.H.{w} L n) :
    Sheaf.H.map ((inverseImageId X).hom.app L) n
        (cohomologyPullback (𝟙 X) L n a) = a := by
  change ((Abelian.Ext.mk₀ _).comp
      (a.mapExactFunctor (inverseImage (𝟙 X))) (zero_add n)).comp
        (Abelian.Ext.mk₀ ((inverseImageId X).hom.app L)) (add_zero n) = a
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mapExactFunctor_comp_mk₀_natTransApp,
    Abelian.Ext.id_mapExactFunctor]
  rw [Abelian.Ext.mk₀_comp_mk₀_assoc, inverseImageId_constant]
  simp

end Identity

section Composition

variable {X S T : Scheme.{u}}
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]
  [HasExt.{w''} (AbelianSheaf.{u, u + 1} T)]

/-- Pullback composes contravariantly after the original inverse-image
comparison, in every cohomological degree. -/
theorem cohomologyPullback_comp (f : S ⟶ X) (g : T ⟶ S)
    (L : AbelianSheaf.{u, u + 1} X) (n : ℕ) (a : Sheaf.H.{w} L n) :
    Sheaf.H.map ((inverseImageComp f g).hom.app L) n
        (cohomologyPullback (g ≫ f) L n a) =
      cohomologyPullback g ((inverseImage f).obj L) n (cohomologyPullback f L n a) := by
  change ((Abelian.Ext.mk₀ _).comp (a.mapExactFunctor (inverseImage (g ≫ f)))
      (zero_add n)).comp (Abelian.Ext.mk₀ ((inverseImageComp f g).hom.app L)) (add_zero n) =
    (Abelian.Ext.mk₀ _).comp
      (((Abelian.Ext.mk₀ _).comp (a.mapExactFunctor (inverseImage f))
        (zero_add n)).mapExactFunctor (inverseImage g)) (zero_add n)
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mapExactFunctor_comp_mk₀_natTransApp,
    Abelian.Ext.comp_mapExactFunctor, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀]
  rw [Abelian.Ext.mk₀_comp_mk₀_assoc, Abelian.Ext.mk₀_comp_mk₀_assoc]
  congr 2
  exact inverseImageComp_constant_inv f g _

end Composition

end AlgebraicGeometry.Scheme.EtaleCohomology

/- Canonical derived-global-sections pullback. These definitions use the
actual derived adjunction and original right-derived functor comparison,
independently of the Ext equivalence. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u dX dS dA

variable {X S : Scheme.{u}}
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}]

/-- The original bounded-below right-derived functor of actual global sections. -/
abbrev derivedGlobalSections (X : Scheme.{u})
    [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)] :
    DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X) ⥤
      DerivedCategory.Plus AddCommGrpCat.{u + 1} :=
  (globalSections X).rightDerivedFunctorPlus

/-- Actual derived direct image followed by actual derived sections is derived
sections on the source, using preservation of injectives by direct image only. -/
def derivedDirectImageGlobalSectionsIso (f : S ⟶ X) :
    derivedDirectImage f ⋙ derivedGlobalSections X ≅ derivedGlobalSections S :=
  (Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives
      (directImage f) (globalSections X)).symm ≪≫
    (directImage f ⋙ globalSections X).rightDerivedFunctorPlusIso
      (directImageGlobalSectionsIso f)

/-- The canonical D+ map on global sections, constructed from the actual
inverse-image/direct-image derived adjunction unit. -/
def derivedGlobalSectionsPullback (f : S ⟶ X)
    (K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X)) :
    (derivedGlobalSections X).obj K ⟶
      (derivedGlobalSections S).obj ((derivedInverseImage f).obj K) :=
  (derivedGlobalSections X).map ((derivedImageAdjunction f).unit.app K) ≫
    (derivedDirectImageGlobalSectionsIso f).hom.app ((derivedInverseImage f).obj K)

/-- The canonical derived map on coefficient singles, with the original
exact-single comparison on the target. -/
def derivedGlobalSectionsPullbackSingle (f : S ⟶ X)
    (L : AbelianSheaf.{u, u + 1} X) :
    (derivedGlobalSections X).obj
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj L) ⟶
      (derivedGlobalSections S).obj
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} S) 0).obj
          ((inverseImage f).obj L)) :=
  derivedGlobalSectionsPullback f
      ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj L) ≫
    (derivedGlobalSections S).map
      (((inverseImage f).rightDerivedFunctorPlusSingleIso 0).hom.app L)

/-- The higher-sections map obtained from homology of the actual canonical D+
map, retaining the native single/homology isomorphisms. -/
def rightDerivedGlobalSectionsPullback (f : S ⟶ X)
    (L : AbelianSheaf.{u, u + 1} X) (n : ℕ) :
    ((globalSections X).rightDerived n).obj L ⟶
      ((globalSections S).rightDerived n).obj ((inverseImage f).obj L) :=
  ((globalSections X).rightDerivedSingleHomologyIso n).hom.app L ≫
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (n : ℤ)).map
      (derivedGlobalSectionsPullbackSingle f L) ≫
    ((globalSections S).rightDerivedSingleHomologyIso n).inv.app ((inverseImage f).obj L)


/-- The direct-image/sections comparison retains both original derived units. -/
@[reassoc]
theorem derivedDirectImageGlobalSectionsIso_unit (f : S ⟶ X)
    (K : CochainComplex.Plus (AbelianSheaf.{u, u + 1} S)) :
    (globalSections X).rightDerivedFunctorPlusUnit.app
        ((directImage f).mapCochainComplexPlus.obj K) ≫
      (derivedGlobalSections X).map ((directImage f).rightDerivedFunctorPlusUnit.app K) ≫
      (derivedDirectImageGlobalSectionsIso f).hom.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (directImageGlobalSectionsIso f)).hom.app K) ≫
      (globalSections S).rightDerivedFunctorPlusUnit.app K := by
  let c := Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives
    (directImage f) (globalSections X)
  let e := (directImage f ⋙ globalSections X).rightDerivedFunctorPlusIso
    (directImageGlobalSectionsIso f)
  have hc := Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app
    (directImage f) (globalSections X) K
  change _ ≫ _ ≫ (c.inv.app _ ≫ e.hom.app _) = _
  rw [← Category.assoc, ← hc]
  simp only [Category.assoc]
  change (directImage f ⋙ globalSections X).rightDerivedFunctorPlusUnit.app K ≫
    c.hom.app (DerivedCategory.Plus.Q.obj K) ≫
      c.inv.app (DerivedCategory.Plus.Q.obj K) ≫ e.hom.app (DerivedCategory.Plus.Q.obj K) = _
  rw [Iso.hom_inv_id_app_assoc]
  exact (directImage f ⋙ globalSections X).rightDerivedFunctorPlusIso_hom_app
    (directImageGlobalSectionsIso f) K

/-- The ordinary section-complex map defined by the original adjunction unit. -/
def globalSectionsPullbackComplex (f : S ⟶ X)
    (K : CochainComplex.Plus (AbelianSheaf.{u, u + 1} X)) :
    (globalSections X).mapCochainComplexPlus.obj K ⟶
      (globalSections S).mapCochainComplexPlus.obj
        ((inverseImage f).mapCochainComplexPlus.obj K) :=
  (globalSections X).mapCochainComplexPlus.map
      ((inverseImageAdjunction f).mapCochainComplexPlus.unit.app K) ≫
    (NatIso.mapCochainComplexPlus (directImageGlobalSectionsIso f)).hom.app
      ((inverseImage f).mapCochainComplexPlus.obj K)

omit [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}] in
/-- Each component is the old ordinary section pullback, not a new map. -/
theorem globalSectionsPullbackComplex_f (f : S ⟶ X)
    (K : CochainComplex.Plus (AbelianSheaf.{u, u + 1} X)) (i : ℤ) :
    (globalSectionsPullbackComplex f K).hom.f i = globalSectionsPullback f (K.obj.X i) := rfl

/-- Coefficient naturality of the actual canonical D+ sections map. -/
@[reassoc]
theorem derivedGlobalSectionsPullback_naturality (f : S ⟶ X)
    {K L : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X)} (q : K ⟶ L) :
    (derivedGlobalSections X).map q ≫ derivedGlobalSectionsPullback f L =
      derivedGlobalSectionsPullback f K ≫
        (derivedGlobalSections S).map ((derivedInverseImage f).map q) := by
  have hη := (derivedImageAdjunction f).unit.naturality q
  change q ≫ (derivedImageAdjunction f).unit.app L =
    (derivedImageAdjunction f).unit.app K ≫
      (derivedDirectImage f).map ((derivedInverseImage f).map q) at hη
  have he := (derivedDirectImageGlobalSectionsIso f).hom.naturality
    ((derivedInverseImage f).map q)
  change (derivedGlobalSections X).map ((derivedDirectImage f).map
      ((derivedInverseImage f).map q)) ≫
        (derivedDirectImageGlobalSectionsIso f).hom.app ((derivedInverseImage f).obj L) =
    (derivedDirectImageGlobalSectionsIso f).hom.app ((derivedInverseImage f).obj K) ≫
      (derivedGlobalSections S).map ((derivedInverseImage f).map q) at he
  dsimp only [derivedGlobalSectionsPullback]
  rw [← CategoryTheory.Functor.map_comp_assoc, hη, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [he]

/-- The canonical D+ map retains the original section map and localization units
on every bounded-below complex. No inverse-image injectivity is assumed. -/
@[reassoc]
theorem derivedGlobalSectionsPullback_unit (f : S ⟶ X)
    (K : CochainComplex.Plus (AbelianSheaf.{u, u + 1} X)) :
    (globalSections X).rightDerivedFunctorPlusUnit.app K ≫
      derivedGlobalSectionsPullback f (DerivedCategory.Plus.Q.obj K) ≫
      (derivedGlobalSections S).map
        ((inverseImage f).rightDerivedFunctorPlusExactComparison.hom.app K) =
    DerivedCategory.Plus.Q.map (globalSectionsPullbackComplex f K) ≫
      (globalSections S).rightDerivedFunctorPlusUnit.app
        ((inverseImage f).mapCochainComplexPlus.obj K) := by
  let l := (inverseImage f).rightDerivedFunctorPlusExactComparison.hom.app K
  have hc := (derivedDirectImageGlobalSectionsIso f).hom.naturality l
  change (derivedGlobalSections X).map ((derivedDirectImage f).map l) ≫
      (derivedDirectImageGlobalSectionsIso f).hom.app
        (DerivedCategory.Plus.Q.obj ((inverseImage f).mapCochainComplexPlus.obj K)) =
    (derivedDirectImageGlobalSectionsIso f).hom.app
      ((derivedInverseImage f).obj (DerivedCategory.Plus.Q.obj K)) ≫
        (derivedGlobalSections S).map l at hc
  dsimp only [l] at hc
  have hu := derivedImageAdjunction_unit_fac f K
  have hA := (globalSections X).rightDerivedFunctorPlusUnit.naturality
    ((inverseImageAdjunction f).mapCochainComplexPlus.unit.app K)
  change DerivedCategory.Plus.Q.map ((globalSections X).mapCochainComplexPlus.map
      ((inverseImageAdjunction f).mapCochainComplexPlus.unit.app K)) ≫
        (globalSections X).rightDerivedFunctorPlusUnit.app
          ((directImage f).mapCochainComplexPlus.obj
            ((inverseImage f).mapCochainComplexPlus.obj K)) =
    (globalSections X).rightDerivedFunctorPlusUnit.app K ≫
      (derivedGlobalSections X).map
        (DerivedCategory.Plus.Q.map
          ((inverseImageAdjunction f).mapCochainComplexPlus.unit.app K)) at hA
  dsimp only [derivedGlobalSectionsPullback]
  simp only [Category.assoc]
  rw [← hc, ← CategoryTheory.Functor.map_comp_assoc, hu, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hA]
  rw [derivedDirectImageGlobalSectionsIso_unit]
  simp only [globalSectionsPullbackComplex, CategoryTheory.Functor.map_comp, Category.assoc]

/-- The compatible lift from the exact image of the source resolution, bundled
in the original bounded-below category. -/
def inverseImageResolutionLiftPlus (f : S ⟶ X)
    {L : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution L)
    (J : InjectiveResolution ((inverseImage f).obj L))
    (φ : InjectiveResolution.ExactFunctor.mappedResolution (inverseImage f) I ⟶
      J.cocomplex) :
    (inverseImage f).mapCochainComplexPlus.obj I.cochainComplexPlus ⟶
      J.cochainComplexPlus :=
  ObjectProperty.homMk
    (InjectiveResolution.ExactFunctor.extendedLift (inverseImage f) I J φ)

omit [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}] in
/-- The lifted augmentation agrees with the original native exact-single map. -/
theorem inverseImageResolutionLiftPlus_augmentation (f : S ⟶ X)
    {L : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution L)
    (J : InjectiveResolution ((inverseImage f).obj L))
    (φ : InjectiveResolution.ExactFunctor.mappedResolution (inverseImage f) I ⟶
      J.cocomplex)
    (hφ : (inverseImage f).map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    (inverseImage f).mapCochainComplexPlus.map I.ιPlus ≫
        inverseImageResolutionLiftPlus f I J φ =
      (show (inverseImage f).mapCochainComplexPlus.obj
          ((CochainComplex.singleFunctorPlus (AbelianSheaf.{u, u + 1} X) 0).obj L) ⟶
          (CochainComplex.singleFunctorPlus (AbelianSheaf.{u, u + 1} S) 0).obj
            ((inverseImage f).obj L) from
        ObjectProperty.homMk
          ((HomologicalComplex.singleMapHomologicalComplex (inverseImage f) (.up ℤ) 0).hom.app L)) ≫
        J.ιPlus := by
  apply ObjectProperty.hom_ext
  change ((inverseImage f).mapHomologicalComplex (.up ℤ)).map I.ι' ≫
      InjectiveResolution.ExactFunctor.extendedLift (inverseImage f) I J φ =
    ((inverseImage f).mapCochainComplexSingleFunctor 0).hom.app L ≫ J.ι'
  apply (cancel_epi (((inverseImage f).mapCochainComplexSingleFunctor 0).inv.app L)).mp
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc] using
    InjectiveResolution.ExactFunctor.extendedLift_augmentation
      (inverseImage f) I J (𝟙 _) φ (by simpa only [Category.id_comp] using hφ)

omit [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}] in
/-- The exact derived comparison carries the lifted resolution augmentation to
the same native exact-single map. -/
theorem inverseImageResolutionLiftPlus_derived_augmentation (f : S ⟶ X)
    {L : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution L)
    (J : InjectiveResolution ((inverseImage f).obj L))
    (φ : InjectiveResolution.ExactFunctor.mappedResolution (inverseImage f) I ⟶
      J.cocomplex)
    (hφ : (inverseImage f).map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    (derivedInverseImage f).map (DerivedCategory.Plus.Q.map I.ιPlus) ≫
        (inverseImage f).rightDerivedFunctorPlusExactComparison.hom.app I.cochainComplexPlus ≫
        DerivedCategory.Plus.Q.map (inverseImageResolutionLiftPlus f I J φ) =
      ((inverseImage f).rightDerivedFunctorPlusSingleIso 0).hom.app L ≫
        DerivedCategory.Plus.Q.map J.ιPlus := by
  let K := (CochainComplex.singleFunctorPlus (AbelianSheaf.{u, u + 1} X) 0).obj L
  let : IsIso (inverseImage f).rightDerivedFunctorPlusUnit :=
    (inverseImage f).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have hn := (inverseImage f).rightDerivedFunctorPlusUnit.naturality I.ιPlus
  change DerivedCategory.Plus.Q.map ((inverseImage f).mapCochainComplexPlus.map I.ιPlus) ≫
      (inverseImage f).rightDerivedFunctorPlusUnit.app I.cochainComplexPlus =
    (inverseImage f).rightDerivedFunctorPlusUnit.app K ≫
      (derivedInverseImage f).map (DerivedCategory.Plus.Q.map I.ιPlus) at hn
  apply (cancel_epi ((inverseImage f).rightDerivedFunctorPlusUnit.app K)).mp
  rw [← Category.assoc, ← hn]
  have hc : (inverseImage f).rightDerivedFunctorPlusUnit.app I.cochainComplexPlus ≫
      (inverseImage f).rightDerivedFunctorPlusExactComparison.hom.app I.cochainComplexPlus =
        𝟙 _ := by
    change (asIso (inverseImage f).rightDerivedFunctorPlusUnit).hom.app _ ≫
      (asIso (inverseImage f).rightDerivedFunctorPlusUnit).inv.app _ = 𝟙 _
    exact (asIso (inverseImage f).rightDerivedFunctorPlusUnit).hom_inv_id_app _
  simp only [Category.assoc]
  rw [← Category.assoc ((inverseImage f).rightDerivedFunctorPlusUnit.app I.cochainComplexPlus),
    hc, Category.id_comp]
  rw [← CategoryTheory.Functor.map_comp, inverseImageResolutionLiftPlus_augmentation f I J φ hφ,
    CategoryTheory.Functor.map_comp]
  erw [← Category.assoc, Functor.rightDerivedFunctorPlusSingleIso_unit]

/-- The canonical D+ sections map equals the independently constructed section
map on supplied resolutions, before taking homology. -/
theorem derivedGlobalSectionsPullbackSingle_resolution (f : S ⟶ X)
    {L : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution L)
    (J : InjectiveResolution ((inverseImage f).obj L))
    (φ : InjectiveResolution.ExactFunctor.mappedResolution (inverseImage f) I ⟶
      J.cocomplex)
    (hφ : (inverseImage f).map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    (I.rightDerivedFunctorPlusIso (globalSections X)).hom ≫
        derivedGlobalSectionsPullbackSingle f L =
      DerivedCategory.Plus.Q.map
        (globalSectionsPullbackComplex f I.cochainComplexPlus ≫
          (globalSections S).mapCochainComplexPlus.map
            (inverseImageResolutionLiftPlus f I J φ)) ≫
        (J.rightDerivedFunctorPlusIso (globalSections S)).hom := by
  apply (cancel_mono ((derivedGlobalSections S).map
    (DerivedCategory.Plus.Q.map J.ιPlus))).mp
  simp only [derivedGlobalSectionsPullbackSingle, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp,
    ← inverseImageResolutionLiftPlus_derived_augmentation f I J φ hφ]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← derivedGlobalSectionsPullback_naturality_assoc]
  rw [InjectiveResolution.rightDerivedFunctorPlusIso_hom_comp_assoc,
    derivedGlobalSectionsPullback_unit_assoc]
  erw [← (globalSections S).rightDerivedFunctorPlusUnit.naturality
    (inverseImageResolutionLiftPlus f I J φ)]
  erw [InjectiveResolution.rightDerivedFunctorPlusIso_hom_comp]
  rfl


/-- Homology of the actual canonical D+ sections map is the independently
defined map of the original section-resolution complexes. -/
theorem rightDerivedGlobalSectionsPullback_eq_resolution (f : S ⟶ X)
    {L : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution L)
    (J : InjectiveResolution ((inverseImage f).obj L))
    (φ : InjectiveResolution.ExactFunctor.mappedResolution (inverseImage f) I ⟶
      J.cocomplex)
    (hφ : (inverseImage f).map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) (n : ℕ) :
    rightDerivedGlobalSectionsPullback f L n =
      (I.isoRightDerivedObjCochain (globalSections X) n).hom ≫
        HomologicalComplex.homologyMap
          (globalSectionsPullbackComplex f I.cochainComplexPlus ≫
            (globalSections S).mapCochainComplexPlus.map
              (inverseImageResolutionLiftPlus f I J φ)).hom (n : ℤ) ≫
        (J.isoRightDerivedObjCochain (globalSections S) n).inv := by
  let H := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (n : ℤ)
  let ψ := globalSectionsPullbackComplex f I.cochainComplexPlus ≫
    (globalSections S).mapCochainComplexPlus.map (inverseImageResolutionLiftPlus f I J φ)
  let pI := (DerivedCategory.Plus.homologyFunctorFactors
    (A := AddCommGrpCat.{u + 1}) (n : ℤ)).app
      ((globalSections X).mapCochainComplexPlus.obj I.cochainComplexPlus)
  let pJ := (DerivedCategory.Plus.homologyFunctorFactors
    (A := AddCommGrpCat.{u + 1}) (n : ℤ)).app
      ((globalSections S).mapCochainComplexPlus.obj J.cochainComplexPlus)
  have hP := (DerivedCategory.Plus.homologyFunctorFactors
    (A := AddCommGrpCat.{u + 1}) (n : ℤ)).hom.naturality ψ
  change H.map (DerivedCategory.Plus.Q.map ψ) ≫ pJ.hom =
    pI.hom ≫ HomologicalComplex.homologyMap ψ.hom (n : ℤ) at hP
  have hP' : pI.inv ≫ H.map (DerivedCategory.Plus.Q.map ψ) =
      HomologicalComplex.homologyMap ψ.hom (n : ℤ) ≫ pJ.inv := by
    apply (cancel_mono pJ.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hP]
    simp only [Iso.inv_hom_id_assoc]
  have hD : H.map (I.rightDerivedFunctorPlusIso (globalSections X)).hom ≫
      H.map (derivedGlobalSectionsPullbackSingle f L) =
    H.map (DerivedCategory.Plus.Q.map ψ) ≫
      H.map (J.rightDerivedFunctorPlusIso (globalSections S)).hom := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg H.map (derivedGlobalSectionsPullbackSingle_resolution f I J φ hφ)
  have hs :
      (I.isoRightDerivedSingleHomology (globalSections X) n).hom ≫
          H.map (derivedGlobalSectionsPullbackSingle f L) =
        ((I.isoRightDerivedObjCochain (globalSections X) n).hom ≫
          HomologicalComplex.homologyMap ψ.hom (n : ℤ) ≫
          (J.isoRightDerivedObjCochain (globalSections S) n).inv) ≫
            (J.isoRightDerivedSingleHomology (globalSections S) n).hom := by
    simp only [InjectiveResolution.isoRightDerivedSingleHomology_hom, Category.assoc]
    rw [hD]
    change (I.isoRightDerivedObjCochain (globalSections X) n).hom ≫
        pI.inv ≫ H.map (DerivedCategory.Plus.Q.map ψ) ≫
          H.map (J.rightDerivedFunctorPlusIso (globalSections S)).hom = _
    rw [← Category.assoc pI.inv, hP']
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  apply (cancel_mono
    (((globalSections S).rightDerivedSingleHomologyIso n).hom.app
      ((inverseImage f).obj L))).mp
  simp only [rightDerivedGlobalSectionsPullback, Category.assoc, Iso.inv_hom_id_app]
  rw [(globalSections X).rightDerivedSingleHomologyIso_hom_app I n,
    (globalSections S).rightDerivedSingleHomologyIso_hom_app J n]
  exact hs

end AlgebraicGeometry.Scheme.EtaleCohomology

/- Comparison with the original Ext cohomological pullback. Generic cycle
normalization is specialized to the actual abelian-group complexes appearing
in the canonical global-sections comparison. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open CochainComplex.HomComplex

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w w' dX dS dA

attribute [local instance] hasSheafifyLarge

/-- The homology class of an explicit section cocycle, using the native
cycle-object and homology projection. -/
def sectionCycleClass (K : CochainComplex AddCommGrpCat.{u + 1} ℤ)
    (n : ℤ) (x : K.X n) (hx : K.d n (n + 1) x = 0) : K.homology n :=
  K.homologyπ n ((K.sc n).abCyclesIso.inv ⟨x, by
    change K.d n ((ComplexShape.up ℤ).next n) x = 0
    rw [CochainComplex.next ℤ n]
    exact hx⟩)

private theorem sectionCycleClass_map
    {K L : CochainComplex AddCommGrpCat.{u + 1} ℤ} (φ : K ⟶ L)
    (n : ℤ) (x : K.X n) (hx : K.d n (n + 1) x = 0) :
    homologyMap φ n (sectionCycleClass K n x hx) =
      sectionCycleClass L n (φ.f n x) (by
        rw [← ConcreteCategory.comp_apply, φ.comm, ConcreteCategory.comp_apply, hx]
        exact map_zero _) := by
  exact HomologicalComplex.addCommGrpCycleClass_map φ n x hx

variable {X S : Scheme.{u}}
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- The actual Gamma comparison on an integer-resolution cocycle, through the
accepted native NT resolution comparison and the actual cycle class. -/
theorem cohomologyRightDerivedAddEquivOfResolution_cocycle
    {L : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution L) (n : ℕ)
    (a : (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ I.cochainComplex.X (n : ℤ))
    (ha : a ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1) = 0) :
    (I.isoRightDerivedObjCochain (globalSections X) n).hom
        (cohomologyRightDerivedAddEquivOfResolution I n
          (I.extEquivCohomologyClass.symm
            (.mk (Cocycle.fromSingleMk a (zero_add (n : ℤ)) ((n : ℤ) + 1) rfl ha)))) =
      let K := ((globalSections X).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
      sectionCycleClass K (n : ℤ)
        ((constantIntegerHomGlobalSectionsIso X).hom.app _ a) (by
          have he : (constantIntegerHomGlobalSectionsIso X).hom.app _
              (a ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1)) =
            (globalSections X).map (I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1))
              ((constantIntegerHomGlobalSectionsIso X).hom.app _ a) :=
            ConcreteCategory.congr_hom
              ((constantIntegerHomGlobalSectionsIso X).hom.naturality
                (I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1))) a
          have hz : (constantIntegerHomGlobalSectionsIso X).hom.app _
              (a ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1)) = 0 := by
            rw [ha]
            exact map_zero _
          exact he.symm.trans hz) := by
  exact InjectiveResolution.extRightDerivedAddEquiv_cocycle_natTrans
    ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (constantIntegerHomGlobalSectionsIso X).hom I n a ha

/-- Normalization of the original natural-degree representative under the
same Gamma comparison. -/
theorem cohomologyRightDerivedAddEquivOfResolution_extMk
    {L : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution L) (n : ℕ)
    (a : (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ I.cocomplex.X n)
    (ha : a ≫ I.cocomplex.d n (n + 1) = 0) :
    (I.isoRightDerivedObjCochain (globalSections X) n).hom
        (cohomologyRightDerivedAddEquivOfResolution I n (I.extMk a (n + 1) rfl ha)) =
      let K := ((globalSections X).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
      sectionCycleClass K (n : ℤ)
        ((constantIntegerHomGlobalSectionsIso X).hom.app _
          (a ≫ (I.cochainComplexXIso n n rfl).inv)) (by
          let a' : (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
              (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ I.cochainComplex.X (n : ℤ) :=
            a ≫ (I.cochainComplexXIso n n rfl).inv
          have ha' : a' ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1) = 0 := by
            rw [I.cochainComplex_d _ _ n (n + 1) rfl (by simp)]
            simp only [a', Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% ha, zero_comp]
          have he : (constantIntegerHomGlobalSectionsIso X).hom.app _
              (a' ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1)) =
            (globalSections X).map (I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1))
              ((constantIntegerHomGlobalSectionsIso X).hom.app _ a') :=
            ConcreteCategory.congr_hom
              ((constantIntegerHomGlobalSectionsIso X).hom.naturality
                (I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1))) a'
          have hz : (constantIntegerHomGlobalSectionsIso X).hom.app _
              (a' ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1)) = 0 := by
            rw [ha']
            exact map_zero _
          exact he.symm.trans hz) := by
  let a' : (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ I.cochainComplex.X (n : ℤ) :=
    a ≫ (I.cochainComplexXIso n n rfl).inv
  have ha' : a' ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1) = 0 := by
    rw [I.cochainComplex_d _ _ n (n + 1) rfl (by simp)]
    simp only [a', Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% ha, zero_comp]
  have hrep : I.extMk a (n + 1) rfl ha =
      I.extEquivCohomologyClass.symm
        (.mk (Cocycle.fromSingleMk a' (zero_add (n : ℤ)) ((n : ℤ) + 1) rfl ha')) := by
    apply I.extEquivCohomologyClass.injective
    rw [Equiv.apply_symm_apply, InjectiveResolution.extEquivCohomologyClass_extMk]
    simp only [a', Nat.cast_add, Nat.cast_one]
  rw [hrep]
  exact cohomologyRightDerivedAddEquivOfResolution_cocycle I n a' ha'

/-- Original Ext pullback agrees with the independently defined resolution
section map, for every actual augmentation-compatible lift. -/
theorem cohomologyRightDerivedAddEquivOfResolution_pullback
    (f : S ⟶ X) {L : AbelianSheaf.{u, u + 1} X}
    (I : InjectiveResolution L) (J : InjectiveResolution ((inverseImage f).obj L))
    (φ : InjectiveResolution.ExactFunctor.mappedResolution (inverseImage f) I ⟶
      J.cocomplex)
    (hφ : (inverseImage f).map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0)
    (n : ℕ) (b : Sheaf.H.{w} L n) :
    cohomologyRightDerivedAddEquivOfResolution J n (cohomologyPullback f L n b) =
      rightDerivedGlobalSectionsPullbackOfLift f I J φ n
        (cohomologyRightDerivedAddEquivOfResolution I n b) := by
  obtain ⟨a, ha, rfl⟩ := I.extMk_surjective b (n + 1) rfl
  apply ((J.isoRightDerivedObjCochain (globalSections S) n).addCommGroupIsoToAddEquiv).injective
  change (J.isoRightDerivedObjCochain (globalSections S) n).hom
      (cohomologyRightDerivedAddEquivOfResolution J n
        (cohomologyPullback f L n (I.extMk a (n + 1) rfl ha))) =
    (J.isoRightDerivedObjCochain (globalSections S) n).hom
      (rightDerivedGlobalSectionsPullbackOfLift f I J φ n
        (cohomologyRightDerivedAddEquivOfResolution I n (I.extMk a (n + 1) rfl ha)))
  rw [cohomologyPullback_extMk_ofLift f I J φ hφ,
    cohomologyRightDerivedAddEquivOfResolution_extMk]
  simp only [rightDerivedGlobalSectionsPullbackOfLift, ConcreteCategory.comp_apply]
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply,
    cohomologyRightDerivedAddEquivOfResolution_extMk, sectionCycleClass_map]
  congr 1
  change (constantIntegerHomGlobalSectionsIso S).hom.app _
      ((((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv ≫
        (inverseImage f).map a ≫ φ.f n) ≫ (J.cochainComplexXIso n n rfl).inv) =
    (globalSectionsResolutionPullback f I J φ).f (n : ℤ)
      ((constantIntegerHomGlobalSectionsIso X).hom.app _
        (a ≫ (I.cochainComplexXIso n n rfl).inv))
  let a' : (constantSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ (inverseImage f).obj
        (I.cochainComplex.X (n : ℤ)) :=
    ((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv ≫
      (inverseImage f).map (a ≫ (I.cochainComplexXIso n n rfl).inv)
  have hn : (constantIntegerHomGlobalSectionsIso S).hom.app _
      (a' ≫ (InjectiveResolution.ExactFunctor.extendedLift (inverseImage f) I J φ).f (n : ℤ)) =
    (globalSections S).map
      ((InjectiveResolution.ExactFunctor.extendedLift (inverseImage f) I J φ).f (n : ℤ))
        ((constantIntegerHomGlobalSectionsIso S).hom.app _ a') :=
    ConcreteCategory.congr_hom
      ((constantIntegerHomGlobalSectionsIso S).hom.naturality
        ((InjectiveResolution.ExactFunctor.extendedLift (inverseImage f) I J φ).f (n : ℤ))) a'
  have hp := constantIntegerHomGlobalSectionsIso_pullback f
    (a ≫ (I.cochainComplexXIso n n rfl).inv)
  have hn' := hn.trans (congrArg
    (fun x => (globalSections S).map
      ((InjectiveResolution.ExactFunctor.extendedLift (inverseImage f) I J φ).f (n : ℤ)) x) hp)
  have hψ : (globalSectionsResolutionPullback f I J φ).f (n : ℤ) =
      globalSectionsPullback f (I.cochainComplex.X (n : ℤ)) ≫
        (globalSections S).map
          ((InjectiveResolution.ExactFunctor.extendedLift (inverseImage f) I J φ).f (n : ℤ)) := rfl
  rw [hψ, ConcreteCategory.comp_apply]
  refine Eq.trans ?_ hn'
  dsimp only [a']
  congr 1
  rw [InjectiveResolution.ExactFunctor.extendedLift_f, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

section CanonicalDerived

variable [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}]

/-- Original Ext-based pullback agrees with homology of the actual canonical
D+ global-sections map, retaining all native resolution and single comparisons. -/
theorem cohomologyRightDerivedAddEquiv_pullback
    (f : S ⟶ X) (L : AbelianSheaf.{u, u + 1} X) (n : ℕ) (a : Sheaf.H.{w} L n) :
    cohomologyRightDerivedAddEquiv ((inverseImage f).obj L) n
        (cohomologyPullback f L n a) =
      rightDerivedGlobalSectionsPullback f L n (cohomologyRightDerivedAddEquiv L n a) := by
  let I := injectiveResolution L
  let J := injectiveResolution ((inverseImage f).obj L)
  let φ := InjectiveResolution.ExactFunctor.lift (inverseImage f) I J (𝟙 _)
  have hφ : (inverseImage f).map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0 := by
    simpa only [Category.id_comp] using
      InjectiveResolution.ExactFunctor.lift_commutes_zero (inverseImage f) I J (𝟙 _)
  rw [rightDerivedGlobalSectionsPullback_eq_resolution f I J φ hφ]
  have hψ :
      (globalSectionsPullbackComplex f I.cochainComplexPlus ≫
        (globalSections S).mapCochainComplexPlus.map
          (inverseImageResolutionLiftPlus f I J φ)).hom =
        globalSectionsResolutionPullback f I J φ := by
    ext i
    rfl
  rw [hψ]
  exact cohomologyRightDerivedAddEquivOfResolution_pullback f I J φ hφ n a

end CanonicalDerived

end AlgebraicGeometry.Scheme.EtaleCohomology
