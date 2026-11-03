/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology.CounitNaturality
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology.SectionsCounitHomology
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Restriction.Resolution
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Restriction
public import Aglib.Algebra.Homology.HomologicalComplex.Adjunction.ResolutionCounit
public import Aglib.Algebra.Homology.ShortComplex.Adjunction.SectionsRestriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pushforward
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections

/-!
# Original affine higher-image restriction on cohomology

For the two actual quasi-isomorphic resolution counits, the original affine
section equivalences carry the native open higher-image comparison to
the original geometric cohomology map. The coefficient arrow is the actual
restriction adjunction unit. The proof retains the original supplied
resolutions, native cycle inclusions and projections, and original Ext
classes. The generic resolution normalization has its sole owner in
`DirectImage.Restriction.Resolution`.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

open CochainComplex HomComplex
open scoped TensorProduct ChangeOfRings


/-- Evaluate the whole original scalar-restricted square before geometric specialization. -/
private theorem restrictScalars_square_apply
    {R S : Type*} [CommRing R] [CommRing S] (σ : R →+* S)
    {A B : ModuleCat R} {C D E : ModuleCat S}
    (u : A ⟶ (ModuleCat.restrictScalars σ).obj C) (v : C ⟶ D) (w : D ⟶ E)
    (a : A ⟶ B) (b : B ⟶ (ModuleCat.restrictScalars σ).obj E)
    (h : u ≫ (ModuleCat.restrictScalars σ).map v ≫
      (ModuleCat.restrictScalars σ).map w = a ≫ b) (x : A) :
    w (v (u x)) = b (a x) :=
  congrArg (fun t : A ⟶ (ModuleCat.restrictScalars σ).obj E => t x) h

section AffineClasses

private def affineCounitUnit (R : CommRingCat.{u})
    (K : CochainComplex (Spec R).Modules ℤ) (n : ℕ) :
    ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K).homology (n : ℤ) ⟶
      moduleSpecΓFunctor.obj (K.homology (n : ℤ)) :=
  (tilde.adjunction (R := R)).homologyCounitMate (K.sc (n : ℤ))

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R))
  (M : X.Modules) (I : InjectiveResolution M)
  [hI : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
    (CommRingCat.of R) (.up ℤ)
    (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex))] (n : ℕ)

private def affineHomologyClass :
    moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward f).rightDerived n).obj M) ⟶
      ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj
        (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj
          I.cochainComplex)).homology (n : ℤ) :=
  moduleHigherDirectImageAffineSectionsHomologyMapOfCounitQuasiIso f M I inferInstance n

private theorem affineHomologyClass_isIso : IsIso (affineHomologyClass f M I n) := by
  exact moduleHigherDirectImageAffineSectionsHomologyMap_isIso_of_counit_quasiIso
    f M I inferInstance n

private theorem affineHomologyClass_counit :
    let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    affineHomologyClass f M I n ≫ affineCounitUnit (CommRingCat.of R) K n =
      moduleSpecΓFunctor.map
        (I.isoRightDerivedObjCochain (Scheme.Modules.pushforward f) n).hom := by
  exact moduleHigherDirectImageAffineSectionsHomologyMap_counit_of_counit_quasiIso
    f M I inferInstance n

private theorem sectionsEquiv_eq_resolutionClass
    (x : moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward f).rightDerived n).obj M)) :
    moduleHigherDirectImageAffineSectionsLinearEquivOfCounitQuasiIso f M I inferInstance n x =
      moduleResolutionSectionsCohomologyLinearEquiv X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) I n
        (homologyMap (moduleSpecPushforwardGlobalSectionsComplexIso
          f (.up ℤ) I.cochainComplex).hom (n : ℤ) (affineHomologyClass f M I n x)) := rfl

end AffineClasses

section Forward

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
  [IsOpenImmersion (Spec.map φ)]

private def sectionsUnit :
    moduleSpecΓFunctor (R := R) ⟶ Scheme.Modules.restrictFunctor (Spec.map φ) ⋙
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom where
  app M := (moduleSpecΓFunctor (R := R)).map
      ((Scheme.Modules.restrictAdjunction (Spec.map φ)).unit.app M) ≫
    (Scheme.Modules.pushforwardGlobalSectionsIso φ).hom.app
      ((Scheme.Modules.restrictFunctor (Spec.map φ)).obj M)
  naturality {M N} v := by
    let G := moduleSpecΓFunctor (R := R)
    let J := Scheme.Modules.restrictFunctor (Spec.map φ)
    let P := Scheme.Modules.pushforward (Spec.map φ)
    let e := (Scheme.Modules.pushforwardGlobalSectionsIso φ).hom
    have hu := congrArg G.map
      ((Scheme.Modules.restrictAdjunction (Spec.map φ)).unit.naturality v)
    simp only [Functor.map_comp, Functor.id_map, Functor.comp_map] at hu
    have he := e.naturality (J.map v)
    change G.map (P.map (J.map v)) ≫ e.app (J.obj N) =
      e.app (J.obj M) ≫ (ModuleCat.restrictScalars φ.hom).map
        ((moduleSpecΓFunctor (R := S)).map (J.map v)) at he
    change G.map v ≫ G.map
        ((Scheme.Modules.restrictAdjunction (Spec.map φ)).unit.app N) ≫ e.app (J.obj N) =
      G.map ((Scheme.Modules.restrictAdjunction (Spec.map φ)).unit.app M) ≫ e.app (J.obj M) ≫
        (ModuleCat.restrictScalars φ.hom).map
          ((moduleSpecΓFunctor (R := S)).map (J.map v))
    rw [← Category.assoc, hu, Category.assoc, he]

private theorem sectionsUnit_apply (M : (Spec R).Modules)
    (x : (moduleSpecΓFunctor (R := R)).obj M) :
    (sectionsUnit φ).app M x =
      (((Scheme.Modules.restrictAdjunction (Spec.map φ)).unit.app M).app ⊤) x := rfl

variable (K : CochainComplex (Spec R).Modules ℤ)
  (L : CochainComplex (Spec S).Modules ℤ)
  (ψ : ((Scheme.Modules.restrictFunctor (Spec.map φ)).mapHomologicalComplex (.up ℤ)).obj K ⟶ L)
  (n : ℤ)

private def sectionsComplexMap :
    ((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex (.up ℤ)).obj
        (((moduleSpecΓFunctor (R := S)).mapHomologicalComplex (.up ℤ)).obj L) :=
  Adjunction.counitSectionsComplexMap
    (G₀ := moduleSpecΓFunctor (R := R)) (G₁ := moduleSpecΓFunctor (R := S))
    (Scheme.Modules.restrictFunctor (Spec.map φ)) (ModuleCat.restrictScalars φ.hom)
    (sectionsUnit φ) K L ψ

private def sectionsHomologyMap :
    (((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℤ)).obj K).homology n ⟶
      (ModuleCat.restrictScalars φ.hom).obj
        ((((moduleSpecΓFunctor (R := S)).mapHomologicalComplex (.up ℤ)).obj L).homology n) :=
  homologyMap (sectionsComplexMap φ K L ψ) n ≫
    (((((moduleSpecΓFunctor (R := S)).mapHomologicalComplex (.up ℤ)).obj L).sc n).mapHomologyIso
      (ModuleCat.restrictScalars φ.hom)).hom

end Forward

section NativeOpen

/-- The standard derived-category structure on the indicated module category. -/
local instance nativeAffineCounitRestrictionStandard (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

variable {R S : CommRingCat.{u}} {X Y : Scheme.{u}}
  (a : Y ⟶ X) (b : Y ⟶ Spec S) (f : X ⟶ Spec R)
  (φ : R ⟶ S)
  [IsOpenImmersion a] [IsOpenImmersion (Spec.map φ)]
  (h : IsPullback a b f (Spec.map φ)) (M : X.Modules)
  (I : InjectiveResolution M)
  (J : InjectiveResolution ((Scheme.Modules.restrictFunctor a).obj M))
  [hI : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
    R (.up ℤ)
    (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex))]
  [hJ : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
    S (.up ℤ)
    (((Scheme.Modules.pushforward b).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex))] (n : ℕ)


private theorem nativeOpen_sectionsHomology :
    let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let L := ((Scheme.Modules.pushforward b).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
    let ψ := (Scheme.Modules.openBaseChangeResolutionMapPlus a b f (Spec.map φ) h M I J).hom
    (sectionsUnit φ).app (((Scheme.Modules.pushforward f).rightDerived n).obj M) ≫
        (ModuleCat.restrictScalars φ.hom).map ((moduleSpecΓFunctor (R := S)).map
          ((Scheme.Modules.higherDirectImageOpenRestrictionIso a b f (Spec.map φ) h n).hom.app M)) ≫
        (ModuleCat.restrictScalars φ.hom).map
          (affineHomologyClass b ((Scheme.Modules.restrictFunctor a).obj M) J n) =
      affineHomologyClass f M I n ≫ sectionsHomologyMap φ K L ψ (n : ℤ) := by
  let A := Scheme.Modules.restrictFunctor (Spec.map φ)
  let N := (Scheme.Modules.restrictFunctor a).obj M
  let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let L := ((Scheme.Modules.pushforward b).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
  let ψ := (Scheme.Modules.openBaseChangeResolutionMapPlus a b f (Spec.map φ) h M I J).hom
  let eI := I.isoRightDerivedObjCochain (Scheme.Modules.pushforward f) n
  let eJ := J.isoRightDerivedObjCochain (Scheme.Modules.pushforward b) n
  let k := (Scheme.Modules.higherDirectImageOpenRestrictionIso a b f (Spec.map φ) h n).hom.app M
  let : IsIso (affineHomologyClass b N J n) := affineHomologyClass_isIso b N J n
  have hk : k = A.map eI.hom ≫
      (((K.sc (n : ℤ)).mapHomologyIso A).inv ≫ homologyMap ψ (n : ℤ)) ≫ eJ.inv := by
    simpa only [Category.assoc] using
      Scheme.Modules.higherDirectImageOpenRestrictionIso_app_resolution
        a b f (Spec.map φ) h M I J n
  exact Adjunction.resolutionCounit_homology
    (tilde.adjunction (R := R)) (tilde.adjunction (R := S))
    A φ.hom (sectionsUnit φ) K L ψ (n : ℤ) eI eJ
    (affineHomologyClass f M I n) (affineHomologyClass b N J n)
    (affineHomologyClass_counit f M I n) (affineHomologyClass_counit b N J n) k hk

private theorem nativeOpen_sectionsHomology_apply
    (x : (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived n).obj M)) :
    let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let L := ((Scheme.Modules.pushforward b).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
    let ψ := (Scheme.Modules.openBaseChangeResolutionMapPlus a b f (Spec.map φ) h M I J).hom
    affineHomologyClass b ((Scheme.Modules.restrictFunctor a).obj M) J n
        ((moduleSpecΓFunctor (R := S)).map
          ((Scheme.Modules.higherDirectImageOpenRestrictionIso a b f (Spec.map φ) h n).hom.app M)
          ((sectionsUnit φ).app (((Scheme.Modules.pushforward f).rightDerived n).obj M) x)) =
      sectionsHomologyMap φ K L ψ (n : ℤ) (affineHomologyClass f M I n x) := by
  exact restrictScalars_square_apply φ.hom _ _ _ _ _
    (nativeOpen_sectionsHomology a b f φ h M I J n) x

omit hI hJ in
private theorem nativeResolutionSections (i : ℤ)
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pushforward f).obj (I.cochainComplex.X i))) :
    (moduleSpecΓFunctor (R := S)).map
        ((Scheme.Modules.openBaseChangeResolutionMapPlus a b f (Spec.map φ) h M I J).hom.f i)
        ((sectionsUnit φ).app ((Scheme.Modules.pushforward f).obj (I.cochainComplex.X i)) x) =
      ((InjectiveResolution.mapCochainComparison (Scheme.Modules.restrictFunctor a) I J).f i).app ⊤
        ((((Scheme.Modules.restrictAdjunction a).unit.app
          (I.cochainComplex.X i)).app ⊤) x) := by
  let P := I.cochainComplex.X i
  let t := InjectiveResolution.mapCochainComparison (Scheme.Modules.restrictFunctor a) I J
  have hu := congrArg (fun z => z.app ⊤ x)
    (Scheme.Modules.cartesianOpenBaseChange_unit a b f (Spec.map φ) h P)
  have hv := congrArg (fun y => (t.f i).app ⊤ y) hu
  change (t.f i).app ⊤
      (((Scheme.Modules.cartesianOpenBaseChange a b f (Spec.map φ) h).hom.app P).app ⊤
        ((((Scheme.Modules.restrictAdjunction (Spec.map φ)).unit.app
          ((Scheme.Modules.pushforward f).obj P)).app ⊤) x)) =
    (t.f i).app ⊤ ((((Scheme.Modules.restrictAdjunction a).unit.app P).app ⊤) x)
  simpa [Scheme.Modules.cartesianPushforwardSquare] using hv.symm

omit hI hJ in
private theorem nativeResolutionComplexSquare :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom
    let β := b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom
    let hs := moduleSectionsBaseChangeScalars a b f φ.hom h.w
    let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let L := ((Scheme.Modules.pushforward b).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
    let ψ := (Scheme.Modules.openBaseChangeResolutionMapPlus a b f (Spec.map φ) h M I J).hom
    sectionsComplexMap φ K L ψ ≫
        ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex (.up ℤ)).map
          (moduleSpecPushforwardGlobalSectionsComplexIso b (.up ℤ) J.cochainComplex).hom =
      (moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ) I.cochainComplex).hom ≫
        moduleResolutionRestrictionSectionsMap a α β φ.hom hs I J := by
  ext i x
  exact nativeResolutionSections a b f φ h M I J i x

omit hI hJ in
private theorem nativeResolutionHomologySquare :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom
    let β := b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom
    let hs := moduleSectionsBaseChangeScalars a b f φ.hom h.w
    let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let L := ((Scheme.Modules.pushforward b).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
    let ψ := (Scheme.Modules.openBaseChangeResolutionMapPlus a b f (Spec.map φ) h M I J).hom
    sectionsHomologyMap φ K L ψ (n : ℤ) ≫
        (ModuleCat.restrictScalars φ.hom).map (homologyMap
          (moduleSpecPushforwardGlobalSectionsComplexIso b (.up ℤ) J.cochainComplex).hom (n : ℤ)) =
      homologyMap
          (moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ) I.cochainComplex).hom (n : ℤ) ≫
        moduleResolutionRestrictionSectionsHomologyMap a α β φ.hom hs I J n := by
  let T := ModuleCat.restrictScalars φ.hom
  let cb := moduleSpecPushforwardGlobalSectionsComplexIso b (.up ℤ) J.cochainComplex
  have hc := congrArg (fun z => homologyMap z (n : ℤ))
    (nativeResolutionComplexSquare a b f φ h M I J)
  simp only [homologyMap_comp] at hc
  have ht := ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor (ModuleCat S) (.up ℤ) (n : ℤ)).map cb.hom) T
  dsimp only [sectionsHomologyMap, moduleResolutionRestrictionSectionsHomologyMap]
  rw [Category.assoc]
  change _ ≫ _ = _ ≫ (_ ≫ _)
  calc
    _ = _ ≫ (homologyMap ((T.mapHomologicalComplex (.up ℤ)).map cb.hom) (n : ℤ) ≫
        (((moduleResolutionSectionComplex Y
          (b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom) J).sc (n : ℤ)).mapHomologyIso T).hom) :=
      congrArg (fun z => _ ≫ z) ht.symm
    _ = _ := by rw [← Category.assoc, hc, Category.assoc]

omit hI hJ in
private theorem nativeResolution_cohomology
    (z : (((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj
        I.cochainComplex)).homology (n : ℤ)) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom
    let β := b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom
    let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let L := ((Scheme.Modules.pushforward b).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
    let ψ := (Scheme.Modules.openBaseChangeResolutionMapPlus a b f (Spec.map φ) h M I J).hom
    moduleResolutionSectionsCohomologyLinearEquiv Y β J n
        (homologyMap (moduleSpecPushforwardGlobalSectionsComplexIso b (.up ℤ) J.cochainComplex).hom
          (n : ℤ) (sectionsHomologyMap φ K L ψ (n : ℤ) z)) =
      moduleCohomologyMapAlong a ((Scheme.Modules.restrictAdjunction a).unit.app M) n
        (moduleResolutionSectionsCohomologyLinearEquiv X α I n
          (homologyMap
            (moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ) I.cochainComplex).hom
            (n : ℤ) z)) := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let β := b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom
  let hs := moduleSectionsBaseChangeScalars a b f φ.hom h.w
  have hab := congrArg ((forget₂ (ModuleCat R) AddCommGrpCat).map)
    (nativeResolutionHomologySquare a b f φ h M I J n)
  simp only [Functor.map_comp, ModuleCat.forget₂_map_restrictScalars] at hab
  have hz := ConcreteCategory.congr_hom hab z
  simp only [ConcreteCategory.comp_apply] at hz
  exact (congrArg (fun t => moduleResolutionSectionsCohomologyLinearEquiv Y β J n t) hz).trans
    (moduleResolutionRestrictionSectionsHomologyMap_cohomology a α β φ.hom hs I J n _)

private theorem sectionsEquiv_openRestriction
    (x : (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived n).obj M)) :
    moduleHigherDirectImageAffineSectionsLinearEquivOfCounitQuasiIso b
        ((Scheme.Modules.restrictFunctor a).obj M) J inferInstance n
        ((moduleSpecΓFunctor (R := S)).map
          ((Scheme.Modules.higherDirectImageOpenRestrictionIso a b f (Spec.map φ) h n).hom.app M)
          ((sectionsUnit φ).app (((Scheme.Modules.pushforward f).rightDerived n).obj M) x)) =
      moduleCohomologyMapAlong a ((Scheme.Modules.restrictAdjunction a).unit.app M) n
        (moduleHigherDirectImageAffineSectionsLinearEquivOfCounitQuasiIso
          f M I inferInstance n x) := by
  let β := b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom
  let cb := moduleSpecPushforwardGlobalSectionsComplexIso b (.up ℤ) J.cochainComplex
  rw [sectionsEquiv_eq_resolutionClass, sectionsEquiv_eq_resolutionClass]
  exact (congrArg
    (fun z => moduleResolutionSectionsCohomologyLinearEquiv Y β J n
      (homologyMap cb.hom (n : ℤ) z))
    (nativeOpen_sectionsHomology_apply a b f φ h M I J n x)).trans
      (nativeResolution_cohomology a b f φ h M I J n (affineHomologyClass f M I n x))

end NativeOpen

-- The native unit and its scalar-forgetting component have deeply nested functor types.
set_option maxRecDepth 2000 in
/-- On an actual affine cartesian open square, the original higher-image comparison
becomes the original geometric cohomology map under the original affine section
comparisons. Only the two original counit witnesses are supplied. -/
theorem moduleHigherDirectImageAffineSectionsLinearEquiv_openRestriction_of_counit_quasiIso
    {R S : CommRingCat.{u}} {X Y : Scheme.{u}}
    (a : Y ⟶ X) (b : Y ⟶ Spec S) (f : X ⟶ Spec R)
    (φ : R ⟶ S)
    [IsOpenImmersion a] [IsOpenImmersion (Spec.map φ)]
    (h : IsPullback a b f (Spec.map φ)) (M : X.Modules)
    (I : InjectiveResolution M)
    (J : InjectiveResolution ((Scheme.Modules.restrictFunctor a).obj M))
  [hI : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
    R (.up ℤ)
    (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex))]
  [hJ : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
    S (.up ℤ)
    (((Scheme.Modules.pushforward b).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex))] (n : ℕ)
    (x : (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived n).obj M)) :
    moduleHigherDirectImageAffineSectionsLinearEquivOfCounitQuasiIso b
        ((Scheme.Modules.restrictFunctor a).obj M) J inferInstance n
        ((moduleSpecΓFunctor (R := S)).map
          ((Scheme.Modules.higherDirectImageOpenRestrictionIso a b f (Spec.map φ) h n).hom.app M)
          ((((Scheme.Modules.restrictAdjunction (Spec.map φ)).unit.app
            (((Scheme.Modules.pushforward f).rightDerived n).obj M)).app ⊤) x)) =
      moduleCohomologyMapAlong a ((Scheme.Modules.restrictAdjunction a).unit.app M) n
        (moduleHigherDirectImageAffineSectionsLinearEquivOfCounitQuasiIso
          f M I inferInstance n x) := by
  exact sectionsEquiv_openRestriction a b f φ h M I J n x

end AlgebraicGeometry.Scheme.Cohomology
