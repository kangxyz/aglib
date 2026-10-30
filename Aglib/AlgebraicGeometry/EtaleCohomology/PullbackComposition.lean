/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.Adjunction
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition
public import Aglib.CategoryTheory.Sites.SheafCohomology.OriginalSections.ExtPullback

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
        (cohomologyPullback (𝟙 X) L n a) = a :=
  by
  let A := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  have hs : (inverseImageConstantIso (𝟙 X)).inv.app A ≫
      (inverseImageId X).hom.app
        ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A) = 𝟙 _ := by
    rw [inverseImageId_constant]
    exact (inverseImageConstantIso (𝟙 X)).inv_hom_id_app A
  exact congrArg (fun k => k a)
    (Functor.extCoefficientTransfer_id (inverseImage (𝟙 X)) (inverseImageId X)
      ((inverseImageConstantIso (𝟙 X)).inv.app A) hs L n)

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
      cohomologyPullback g ((inverseImage f).obj L) n (cohomologyPullback f L n a) :=
  Functor.extPrecompMap_comparison (inverseImage f) (inverseImage g)
    (inverseImage (g ≫ f)) (inverseImageComp f g)
    ((inverseImageConstantIso f).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    ((inverseImageConstantIso g).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    ((inverseImageConstantIso (g ≫ f)).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (inverseImageComp_constant_inv f g _) L n a

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
  Adjunction.derivedRightSectionsIso (inverseImageAdjunction f) (globalSections X)
    (directImageGlobalSectionsIso f)

/-- The canonical D+ map on global sections, constructed from the actual
inverse-image/direct-image derived adjunction unit. -/
def derivedGlobalSectionsPullback (f : S ⟶ X)
    (K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X)) :
    (derivedGlobalSections X).obj K ⟶
      (derivedGlobalSections S).obj ((derivedInverseImage f).obj K) :=
  Adjunction.derivedUnitSectionsPullback (inverseImageAdjunction f) (globalSections X)
    (directImageGlobalSectionsIso f) K

/-- The canonical derived map on coefficient singles, with the original
exact-single comparison on the target. -/
def derivedGlobalSectionsPullbackSingle (f : S ⟶ X)
    (L : AbelianSheaf.{u, u + 1} X) :
    (derivedGlobalSections X).obj
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj L) ⟶
      (derivedGlobalSections S).obj
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} S) 0).obj
          ((inverseImage f).obj L)) :=
  Adjunction.derivedUnitSectionsPullbackSingle (inverseImageAdjunction f) (globalSections X)
    (directImageGlobalSectionsIso f) L

/-- The higher-sections map obtained from homology of the actual canonical D+
map, retaining the native single/homology isomorphisms. -/
def rightDerivedGlobalSectionsPullback (f : S ⟶ X)
    (L : AbelianSheaf.{u, u + 1} X) (n : ℕ) :
    ((globalSections X).rightDerived n).obj L ⟶
      ((globalSections S).rightDerived n).obj ((inverseImage f).obj L) :=
  Adjunction.rightDerivedUnitSectionsPullback (inverseImageAdjunction f) (globalSections X)
    (directImageGlobalSectionsIso f) L n

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
      (globalSections S).rightDerivedFunctorPlusUnit.app K :=
  Adjunction.derivedRightSectionsIso_unit (inverseImageAdjunction f) (globalSections X)
    (directImageGlobalSectionsIso f) K

/-- The ordinary section-complex map defined by the original adjunction unit. -/
def globalSectionsPullbackComplex (f : S ⟶ X)
    (K : CochainComplex.Plus (AbelianSheaf.{u, u + 1} X)) :
    (globalSections X).mapCochainComplexPlus.obj K ⟶
      (globalSections S).mapCochainComplexPlus.obj
        ((inverseImage f).mapCochainComplexPlus.obj K) :=
  Adjunction.unitSectionsPullbackComplex (inverseImageAdjunction f) (globalSections X)
    (directImageGlobalSectionsIso f) K

omit [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}] in
/-- Each component is the old ordinary section pullback, not a new map. -/
theorem globalSectionsPullbackComplex_f (f : S ⟶ X)
    (K : CochainComplex.Plus (AbelianSheaf.{u, u + 1} X)) (i : ℤ) :
    (globalSectionsPullbackComplex f K).hom.f i = globalSectionsPullback f (K.obj.X i) :=
  Adjunction.unitSectionsPullbackComplex_f (inverseImageAdjunction f) (globalSections X)
    (directImageGlobalSectionsIso f) K i

/-- Coefficient naturality of the actual canonical D+ sections map. -/
@[reassoc]
theorem derivedGlobalSectionsPullback_naturality (f : S ⟶ X)
    {K L : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X)} (q : K ⟶ L) :
    (derivedGlobalSections X).map q ≫ derivedGlobalSectionsPullback f L =
      derivedGlobalSectionsPullback f K ≫
        (derivedGlobalSections S).map ((derivedInverseImage f).map q) :=
  Adjunction.derivedUnitSectionsPullback_naturality (inverseImageAdjunction f) (globalSections X)
    (directImageGlobalSectionsIso f) q

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
        ((inverseImage f).mapCochainComplexPlus.obj K) :=
  Adjunction.derivedUnitSectionsPullback_unit (inverseImageAdjunction f) (globalSections X)
    (directImageGlobalSectionsIso f) K

/-- The compatible lift from the exact image of the source resolution, bundled
in the original bounded-below category. -/
def inverseImageResolutionLiftPlus (f : S ⟶ X)
    {L : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution L)
    (J : InjectiveResolution ((inverseImage f).obj L))
    (φ : InjectiveResolution.ExactFunctor.mappedResolution (inverseImage f) I ⟶
      J.cocomplex) :
    (inverseImage f).mapCochainComplexPlus.obj I.cochainComplexPlus ⟶
      J.cochainComplexPlus :=
  Adjunction.resolutionLiftPlus (F := inverseImage f) I J φ

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
        J.ιPlus :=
  Adjunction.resolutionLiftPlus_augmentation (F := inverseImage f) I J φ hφ

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
        DerivedCategory.Plus.Q.map J.ιPlus :=
  Adjunction.resolutionLiftPlus_derived_augmentation (F := inverseImage f) I J φ hφ

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
        (J.rightDerivedFunctorPlusIso (globalSections S)).hom :=
  Adjunction.derivedUnitSectionsPullbackSingle_resolution (inverseImageAdjunction f)
    (globalSections X)
    (directImageGlobalSectionsIso f) I J φ hφ

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
        (J.isoRightDerivedObjCochain (globalSections S) n).inv :=
  Adjunction.rightDerivedUnitSectionsPullback_eq_resolution (inverseImageAdjunction f)
    (globalSections X)
    (directImageGlobalSectionsIso f) I J φ hφ n

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
  Adjunction.originalSectionCycleClass K n x hx

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
          exact he.symm.trans hz) :=
  Adjunction.originalSectionsExtEquivOfResolution_cocycle (constantAdjunction X) I n a ha

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
          exact he.symm.trans hz) :=
  Adjunction.originalSectionsExtEquivOfResolution_extMk (constantAdjunction X) I n a ha

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
        (cohomologyRightDerivedAddEquivOfResolution I n b) :=
  Adjunction.originalSectionsExtEquivOfResolution_pullback (constantAdjunction X)
    (inverseImageAdjunction f) (constantAdjunction S)
    (directImageGlobalSectionsIso f) (inverseImageConstantIso f)
    (inverseImageConstantCanonicalIso_eq f).symm I J φ hφ n b

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
      rightDerivedGlobalSectionsPullback f L n (cohomologyRightDerivedAddEquiv L n a) :=
  Adjunction.originalSectionsExtEquiv_pullback (constantAdjunction X)
    (inverseImageAdjunction f) (constantAdjunction S)
    (directImageGlobalSectionsIso f) (inverseImageConstantIso f)
    (inverseImageConstantCanonicalIso_eq f).symm L n a

end CanonicalDerived

end AlgebraicGeometry.Scheme.EtaleCohomology
