/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.Adjunction.FollowedUnit
public import Aglib.Algebra.Homology.HomologicalComplex.Adjunction.ResolutionCounit.Values
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.FlatComparison.Resolution
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.FlatComparison.AffineSections
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.Affine
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Pullback

/-!
# The original flat higher-image map in affine cohomology coordinates

The original native resolution comparison and actual cartesian coefficient
arrow identify the installed flat higher-image map with geometric pullback
on the unchanged cohomology. Native affine counit mates retain the original
cycle classes; global sections need not preserve homology. The unit formula
then identifies the same map with the nonflat affine comparison.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

open FlatComparison

section AffineClasses

/-- The native counit mate on homology of the original affine section complex. -/
private def affineCounitUnit (R : CommRingCat.{u})
    (K : CochainComplex (Spec R).Modules ℤ) (n : ℕ) :
    ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K).homology (n : ℤ) ⟶
      moduleSpecΓFunctor.obj (K.homology (n : ℤ)) :=
  (tilde.adjunction (R := R)).homologyCounitMate (K.sc (n : ℤ))

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
  (M : X.Modules) [M.IsQuasicoherent] (I : InjectiveResolution M) (n : ℕ)

/-- The original affine higher-image section and homology comparison. -/
private def affineHomologyClass :
    moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward f).rightDerived n).obj M) ⟶
      ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj
        (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj
          I.cochainComplex)).homology (n : ℤ) :=
  moduleHigherDirectImageAffineSectionsHomologyMap f M I n

/-- The original affine section and homology comparison is invertible. -/
private theorem affineHomologyClass_isIso : IsIso (affineHomologyClass f M I n) := by
  exact moduleHigherDirectImageAffineSectionsHomologyMap_isIso f M I n

/-- The original affine class retains the native counit and resolution comparison. -/
private theorem affineHomologyClass_counit :
    let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    affineHomologyClass f M I n ≫ affineCounitUnit (CommRingCat.of R) K n =
      moduleSpecΓFunctor.map
        (I.isoRightDerivedObjCochain (Scheme.Modules.pushforward f) n).hom := by
  exact moduleHigherDirectImageAffineSectionsHomologyMap_counit f M I n

/-- The original affine cohomology equivalence retains the original resolution class. -/
private theorem sectionsEquiv_eq_resolutionClass
    (x : moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward f).rightDerived n).obj M)) :
    moduleHigherDirectImageAffineSectionsLinearEquiv f M I n x =
      moduleResolutionSectionsCohomologyLinearEquiv X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) I n
        (homologyMap (moduleSpecPushforwardGlobalSectionsComplexIso
          f (.up ℤ) I.cochainComplex).hom (n : ℤ) (affineHomologyClass f M I n x)) := rfl

end AffineClasses

section NativeFlat

/-- The standard derived-category structure on the indicated module category. -/
local instance flatAffineComparisonStandard (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

variable {R S : CommRingCat.{u}} {X Y : Scheme.{u}}
  (a : Y ⟶ X) (b : Y ⟶ Spec S) (f : X ⟶ Spec R)
  [QuasiCompact f] [QuasiSeparated f] (φ : R ⟶ S)
  [Flat a] [Flat (Spec.map φ)]
  (h : IsPullback a b f (Spec.map φ)) (M : X.Modules) [M.IsQuasicoherent]
  (I : InjectiveResolution M)
  (J : InjectiveResolution ((Scheme.Modules.pullback a).obj M)) (n : ℕ)

omit [QuasiCompact f] [QuasiSeparated f] [M.IsQuasicoherent] [Flat (Spec.map φ)] in
/-- Each actual resolved cartesian component retains the original geometric unit. -/
private theorem nativeResolutionSections (i : ℤ)
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pushforward f).obj (I.cochainComplex.X i))) :
    (moduleSpecΓFunctor (R := S)).map
        ((Scheme.Modules.flatBaseChangeResolutionMapPlus a b f (Spec.map φ) h M I J).hom.f i)
        ((sectionsUnit φ).app ((Scheme.Modules.pushforward f).obj (I.cochainComplex.X i)) x) =
      ((InjectiveResolution.mapCochainComparison (Scheme.Modules.pullback a) I J).f i).app ⊤
        ((((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
          (I.cochainComplex.X i)).app ⊤) x) := by
  let P := I.cochainComplex.X i
  let t := InjectiveResolution.mapCochainComparison (Scheme.Modules.pullback a) I J
  have hu := congrArg (fun z => z.app ⊤ x)
    (Scheme.Modules.cartesianBaseChangeMap_unit a b f (Spec.map φ) h P)
  have hv := congrArg (fun y => (t.f i).app ⊤ y) hu
  change (t.f i).app ⊤
      (((Scheme.Modules.cartesianBaseChangeMap a b f (Spec.map φ) h).app P).app ⊤
        ((((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
          ((Scheme.Modules.pushforward f).obj P)).app ⊤) x)) =
    (t.f i).app ⊤ ((((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app P).app ⊤) x)
  simpa [Scheme.Modules.cartesianPushforwardSquare] using hv.symm

omit [QuasiCompact f] [QuasiSeparated f] [M.IsQuasicoherent] [Flat (Spec.map φ)] in
/-- The original flat resolution arrow gives the actual square of section complexes. -/
private theorem nativeResolutionComplexSquare :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom
    let β := b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom
    let hs := moduleSectionsBaseChangeScalars a b f φ.hom h.w
    let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let L := ((Scheme.Modules.pushforward b).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
    let ψ := (Scheme.Modules.flatBaseChangeResolutionMapPlus a b f (Spec.map φ) h M I J).hom
    Adjunction.counitSectionsComplexMap (Scheme.Modules.pullback (Spec.map φ))
        (ModuleCat.restrictScalars φ.hom) (sectionsUnit φ) K L ψ ≫
        ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex (.up ℤ)).map
          (moduleSpecPushforwardGlobalSectionsComplexIso b (.up ℤ) J.cochainComplex).hom =
      (moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ) I.cochainComplex).hom ≫
        moduleResolutionPullbackSectionsMap a α β φ.hom hs I J := by
  ext i x
  exact nativeResolutionSections a b f φ h M I J i x

omit [QuasiCompact f] [QuasiSeparated f] [M.IsQuasicoherent] [Flat (Spec.map φ)] in
/-- The actual restriction-complex homology has the original geometric cohomology value. -/
private theorem nativeResolutionCohomology
    (z : (moduleResolutionSectionComplex X
      (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom) I).homology (n : ℤ)) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom
    let β := b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom
    let hs := moduleSectionsBaseChangeScalars a b f φ.hom h.w
    let D := moduleResolutionSectionComplex Y β J
    moduleResolutionSectionsCohomologyLinearEquiv Y β J n
        (((D.sc (n : ℤ)).mapHomologyIso (ModuleCat.restrictScalars φ.hom)).hom
          (homologyMap (moduleResolutionPullbackSectionsMap a α β φ.hom hs I J) (n : ℤ) z)) =
      moduleCohomologyMapAlong a ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M) n
        (moduleResolutionSectionsCohomologyLinearEquiv X α I n z) := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let β := b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom
  let hs := moduleSectionsBaseChangeScalars a b f φ.hom h.w
  let C := moduleResolutionSectionComplex X α I
  let D := moduleResolutionSectionComplex Y β J
  let δ := moduleResolutionPullbackSectionsTensorMap a α β φ.hom hs I J
  let r := moduleResolutionPullbackSectionsMap a α β φ.hom hs I J
  have hr : r.f (n : ℤ) = (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (C.X (n : ℤ)) ≫
      (ModuleCat.restrictScalars φ.hom).map (δ.f (n : ℤ)) := by
    exact (congrArg (fun t => t.f (n : ℤ))
      (moduleResolutionPullbackSectionsTensorMap_unit a α β φ.hom hs I J)).symm
  have hz := extendScalarsHomologyMap_followed_one_tmul φ.hom C D δ r (n : ℤ) hr z
  exact (congrArg (moduleResolutionSectionsCohomologyLinearEquiv Y β J n) hz.symm).trans
    (moduleResolutionPullbackSectionsHomologyMap_one_tmul a α β φ.hom hs I J n z)

variable [QuasiCompact b] [QuasiSeparated b]

/-- The original affine cohomology equivalence identifies the actual flat higher-image map. -/
private theorem sectionsEquiv_flatBaseChange
    (x : (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived n).obj M)) :
    moduleHigherDirectImageAffineSectionsLinearEquiv b
        ((Scheme.Modules.pullback a).obj M) J n
        ((moduleSpecΓFunctor (R := S)).map
          ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f (Spec.map φ) h n).app M)
          ((sectionsUnit φ).app (((Scheme.Modules.pushforward f).rightDerived n).obj M) x)) =
      moduleCohomologyMapAlong a ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M) n
        (moduleHigherDirectImageAffineSectionsLinearEquiv f M I n x) := by
  let A := Scheme.Modules.pullback (Spec.map φ)
  let N := (Scheme.Modules.pullback a).obj M
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let β := b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom
  let hs := moduleSectionsBaseChangeScalars a b f φ.hom h.w
  let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let L := ((Scheme.Modules.pushforward b).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
  let ψ := (Scheme.Modules.flatBaseChangeResolutionMapPlus a b f (Spec.map φ) h M I J).hom
  let eI := I.isoRightDerivedObjCochain (Scheme.Modules.pushforward f) n
  let eJ := J.isoRightDerivedObjCochain (Scheme.Modules.pushforward b) n
  let k := (Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f (Spec.map φ) h n).app M
  let : IsIso (affineHomologyClass b N J n) := affineHomologyClass_isIso b N J n
  have hk := Scheme.Modules.higherDirectImageFlatBaseChangeMap_app_resolution
    a b f (Spec.map φ) h M I J n
  exact Adjunction.resolutionCounit_cohomology_original_values
    (tilde.adjunction (R := R)) (tilde.adjunction (R := S)) A φ.hom (sectionsUnit φ)
    K L ψ (n : ℤ) eI eJ (affineHomologyClass f M I n) (affineHomologyClass b N J n)
    (affineHomologyClass_counit f M I n) (affineHomologyClass_counit b N J n) k hk
    (moduleResolutionSectionComplex X α I) (moduleResolutionSectionComplex Y β J)
    (moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ) I.cochainComplex).hom
    (moduleSpecPushforwardGlobalSectionsComplexIso b (.up ℤ) J.cochainComplex).hom
    (moduleResolutionPullbackSectionsMap a α β φ.hom hs I J)
    (nativeResolutionComplexSquare a b f φ h M I J)
    (moduleResolutionSectionsCohomologyLinearEquiv X α I n)
    (moduleResolutionSectionsCohomologyLinearEquiv Y β J n)
    (moduleCohomologyMapAlong a ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M) n)
    (nativeResolutionCohomology a b f φ h M I J n)
    (moduleHigherDirectImageAffineSectionsLinearEquiv f M I n)
    (moduleHigherDirectImageAffineSectionsLinearEquiv b N J n)
    (sectionsEquiv_eq_resolutionClass f M I n)
    (sectionsEquiv_eq_resolutionClass b N J n) x

end NativeFlat


/-- On an actual affine flat cartesian square, the installed higher-image comparison
has the original geometric pullback formula on the actual global-section unit.
Target qcqs and flatness of the source leg follow from the cartesian square. -/
theorem moduleHigherDirectImageAffineSectionsLinearEquiv_flatBaseChange_unit
    {R S : CommRingCat.{u}} {X Y : Scheme.{u}}
    (a : Y ⟶ X) (b : Y ⟶ Spec S) (f : X ⟶ Spec R)
    [QuasiCompact f] [QuasiSeparated f] (φ : R ⟶ S) [Flat (Spec.map φ)]
    (h : IsPullback a b f (Spec.map φ)) (M : X.Modules) [M.IsQuasicoherent]
    (I : InjectiveResolution M)
    (J : InjectiveResolution ((Scheme.Modules.pullback a).obj M)) (n : ℕ)
    (x : (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived n).obj M)) :
    let := Scheme.Modules.flat_cartesian_baseChange a b f (Spec.map φ) h
    let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
    let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
    moduleHigherDirectImageAffineSectionsLinearEquiv b
        ((Scheme.Modules.pullback a).obj M) J n
        ((moduleSpecΓFunctor (R := S)).map
          ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f (Spec.map φ) h n).app M)
          ((((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
            (((Scheme.Modules.pushforward f).rightDerived n).obj M)).app ⊤) x)) =
      moduleCohomologyMapAlong a
        ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M) n
        (moduleHigherDirectImageAffineSectionsLinearEquiv f M I n x) := by
  let := Scheme.Modules.flat_cartesian_baseChange a b f (Spec.map φ) h
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  exact sectionsEquiv_flatBaseChange a b f φ h M I J n x

/-- The original flat higher-image map carries a unit pure tensor to actual geometric
pullback under the unchanged affine cohomology equivalences. -/
theorem moduleHigherDirectImageAffineSectionsLinearEquiv_flatBaseChange_one_tmul
    {R S : CommRingCat.{u}} {X Y : Scheme.{u}}
    (a : Y ⟶ X) (b : Y ⟶ Spec S) (f : X ⟶ Spec R)
    [QuasiCompact f] [QuasiSeparated f] (φ : R ⟶ S) [Flat (Spec.map φ)]
    (h : IsPullback a b f (Spec.map φ)) (M : X.Modules) [M.IsQuasicoherent]
    (I : InjectiveResolution M)
    (J : InjectiveResolution ((Scheme.Modules.pullback a).obj M)) (n : ℕ)
    (x : (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived n).obj M)) :
    let := Scheme.Modules.flat_cartesian_baseChange a b f (Spec.map φ) h
    let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
    let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
    let := moduleHigherDirectImageAffine_isQuasicoherent f M n
    moduleHigherDirectImageAffineSectionsLinearEquiv b
        ((Scheme.Modules.pullback a).obj M) J n
        ((moduleSpecΓFunctor (R := S)).map
          ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f (Spec.map φ) h n).app M)
          ((Scheme.Modules.affinePullbackGlobalSectionsIso φ
            (((Scheme.Modules.pushforward f).rightDerived n).obj M)).hom
              ((1 : S) ⊗ₜ[R,φ.hom] x))) =
      moduleCohomologyMapAlong a
        ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M) n
        (moduleHigherDirectImageAffineSectionsLinearEquiv f M I n x) := by
  let := Scheme.Modules.flat_cartesian_baseChange a b f (Spec.map φ) h
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  let := moduleHigherDirectImageAffine_isQuasicoherent f M n
  dsimp only
  have hx := Scheme.Modules.affinePullbackGlobalSectionsIso_one_tmul φ
    (((Scheme.Modules.pushforward f).rightDerived n).obj M) x
  exact (congrArg (fun y =>
    moduleHigherDirectImageAffineSectionsLinearEquiv b ((Scheme.Modules.pullback a).obj M) J n
      ((moduleSpecΓFunctor (R := S)).map
        ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f (Spec.map φ) h n).app M) y))
      hx).trans
    (moduleHigherDirectImageAffineSectionsLinearEquiv_flatBaseChange_unit a b f φ h M I J n x)

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Modules

open Cohomology

set_option maxHeartbeats 800000 in
-- The original scalar and native higher-image actions cross the two cohomology universes here.
/-- On an affine flat cartesian square, the original flat higher-image component is
exactly the actual affine nonflat comparison, with its original geometric coefficient unit. -/
theorem higherDirectImageFlatBaseChangeMap_app_eq_affineMap
    {R S : CommRingCat.{u}} {X Y : Scheme.{u}}
    (a : Y ⟶ X) (b : Y ⟶ Spec S) (f : X ⟶ Spec R)
    [QuasiCompact f] [QuasiSeparated f] (φ : R ⟶ S) [Flat (Spec.map φ)]
    (h : IsPullback a b f (Spec.map φ)) (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    let := flat_cartesian_baseChange a b f (Spec.map φ) h
    let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
    let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
    (higherDirectImageFlatBaseChangeMap a b f (Spec.map φ) h n).app M =
      higherDirectImageAffineMap (M := M) (N := (pullback a).obj M) a b f φ h.w
        ((pullbackPushforwardAdjunction a).unit.app M) n := by
  let := flat_cartesian_baseChange a b f (Spec.map φ) h
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  refine higherDirectImageAffineMap_eq_of_one_tmul
    (M := M) (N := (pullback a).obj M) a b f φ h.w
    ((pullbackPushforwardAdjunction a).unit.app M) n
    ((higherDirectImageFlatBaseChangeMap a b f (Spec.map φ) h n).app M) ?_
  dsimp only
  intro x
  exact moduleHigherDirectImageAffineSectionsLinearEquiv_flatBaseChange_one_tmul
    a b f φ h M (injectiveResolution M) (injectiveResolution ((pullback a).obj M)) n x

end AlgebraicGeometry.Scheme.Modules
