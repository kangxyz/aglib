/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

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

/-- The original section complex of the supplied pushed-forward resolution. -/
private abbrev affineSectionsComplex : CochainComplex (ModuleCat.{u} R) ℤ :=
  (moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj
    (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)

/-- The original affine cohomology equivalence retains every native cycle projection. -/
private theorem sectionsEquiv_homologyπ
    (x : moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward f).rightDerived n).obj M))
    (c : (affineSectionsComplex f M I).cycles (n : ℤ))
    (hc : affineHomologyClass f M I n x = (affineSectionsComplex f M I).homologyπ (n : ℤ) c) :
    moduleHigherDirectImageAffineSectionsLinearEquiv f M I n x =
      moduleResolutionSectionClass X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) I n
        ((moduleResolutionSectionCyclesIso X
          (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) I n).hom
            (HomologicalComplex.cyclesMap
              (moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ) I.cochainComplex).hom
                (n : ℤ) c)) := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let C := affineSectionsComplex f M I
  let cf := moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ) I.cochainComplex
  rw [sectionsEquiv_eq_resolutionClass f M I n x, hc]
  have hπ := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality cf.hom (n : ℤ)) c
  change homologyMap cf.hom (n : ℤ) (C.homologyπ (n : ℤ) c) =
    (moduleResolutionSectionComplex X α I).homologyπ (n : ℤ)
      (HomologicalComplex.cyclesMap cf.hom (n : ℤ) c) at hπ
  rw [hπ, moduleResolutionSectionsCohomologyLinearEquiv_homologyπ X α I n]

/-- The original affine section cycle in structural global-section coordinates. -/
private def affineSectionCycle
    (c : (affineSectionsComplex f M I).cycles (n : ℤ)) :
    moduleResolutionSectionCycles X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) I n :=
  (moduleResolutionSectionCyclesIso X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) I n).hom
      (cyclesMap (moduleSpecPushforwardGlobalSectionsComplexIso
        f (.up ℤ) I.cochainComplex).hom (n : ℤ) c)

omit [QuasiCompact f] [QuasiSeparated f] [M.IsQuasicoherent] in
/-- The affine section cycle retains its original underlying section value. -/
private theorem affineSectionCycle_val
    (c : (affineSectionsComplex f M I).cycles (n : ℤ)) :
    (affineSectionCycle f M I n c).val = (affineSectionsComplex f M I).iCycles (n : ℤ) c := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let cf := moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ) I.cochainComplex
  rw [affineSectionCycle, moduleResolutionSectionCyclesIso_hom_val]
  have hi := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i cf.hom (n : ℤ)) c
  change (moduleResolutionSectionComplex X α I).iCycles (n : ℤ)
      (cyclesMap cf.hom (n : ℤ) c) = _
  change (moduleResolutionSectionComplex X α I).iCycles (n : ℤ)
      (cyclesMap cf.hom (n : ℤ) c) =
    cf.hom.f (n : ℤ) ((affineSectionsComplex f M I).iCycles (n : ℤ) c) at hi
  exact hi.trans rfl

/-- The original inverse comparison on affine section cycles. -/
private def affineSectionCycleInverse
    (s : moduleResolutionSectionCycles X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) I n) :
    (affineSectionsComplex f M I).cycles (n : ℤ) :=
  cyclesMap (moduleSpecPushforwardGlobalSectionsComplexIso
      f (.up ℤ) I.cochainComplex).inv (n : ℤ)
    ((moduleResolutionSectionCyclesIso X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) I n).inv s)

omit [QuasiCompact f] [QuasiSeparated f] [M.IsQuasicoherent] in
/-- The inverse affine section cycle retains the original cycle inclusion. -/
private theorem affineSectionCycleInverse_iCycles
    (s : moduleResolutionSectionCycles X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) I n) :
    (affineSectionsComplex f M I).iCycles (n : ℤ)
        (affineSectionCycleInverse f M I n s) = s.val := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let cf := moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ) I.cochainComplex
  let e := moduleResolutionSectionCyclesIso X α I n
  have hi := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i cf.inv (n : ℤ)) (e.inv s)
  have hs := moduleResolutionSectionCyclesIso_hom_val X α I n (e.inv s)
  have he := ConcreteCategory.congr_hom e.inv_hom_id s
  change e.hom (e.inv s) = s at he
  rw [he] at hs
  change (affineSectionsComplex f M I).iCycles (n : ℤ)
      (cyclesMap cf.inv (n : ℤ) (e.inv s)) = _
  change (affineSectionsComplex f M I).iCycles (n : ℤ)
      (cyclesMap cf.inv (n : ℤ) (e.inv s)) =
    cf.inv.f (n : ℤ) ((moduleResolutionSectionComplex X α I).iCycles (n : ℤ) (e.inv s)) at hi
  exact hi.trans ((congrArg (cf.inv.f (n : ℤ)) hs.symm).trans rfl)

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

/-- The actual flat higher-image map retains the original forwarded homology class. -/
private theorem nativeFlat_affineClass
    (x : (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived n).obj M)) :
    let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let L := ((Scheme.Modules.pushforward b).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
    let ψ := (Scheme.Modules.flatBaseChangeResolutionMapPlus a b f (Spec.map φ) h M I J).hom
    (moduleSpecΓFunctor (R := S)).map
        (J.isoRightDerivedObjCochain (Scheme.Modules.pushforward b) n).hom
        ((moduleSpecΓFunctor (R := S)).map
          ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f (Spec.map φ) h n).app M)
          ((sectionsUnit φ).app (((Scheme.Modules.pushforward f).rightDerived n).obj M) x)) =
      homologyForward φ K L ψ (n : ℤ) (affineHomologyClass f M I n x) := by
  let F := Scheme.Modules.pushforward f
  let B := Scheme.Modules.pushforward b
  let A := Scheme.Modules.pullback (Spec.map φ)
  let G := moduleSpecΓFunctor (R := S)
  let K := (F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let L := (B.mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
  let ψ := (Scheme.Modules.flatBaseChangeResolutionMapPlus a b f (Spec.map φ) h M I J).hom
  let eI := I.isoRightDerivedObjCochain F n
  let eJ := J.isoRightDerivedObjCochain B n
  let eH := (K.sc (n : ℤ)).mapHomologyIso A
  let k := (Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f (Spec.map φ) h n).app M
  have hk := congrArg (fun t => t ≫ eJ.hom)
    (Scheme.Modules.higherDirectImageFlatBaseChangeMap_app_resolution
      a b f (Spec.map φ) h M I J n)
  simp only [Category.assoc] at hk
  change k ≫ eJ.hom = A.map eI.hom ≫ eH.inv ≫ homologyMap ψ (n : ℤ) ≫
    eJ.inv ≫ eJ.hom at hk
  rw [eJ.inv_hom_id] at hk
  erw [Category.comp_id] at hk
  have hG := congrArg G.map hk
  simp only [Functor.map_comp] at hG
  have hx := ConcreteCategory.congr_hom hG ((sectionsUnit φ).app (((F.rightDerived n).obj M)) x)
  change G.map eJ.hom (G.map k ((sectionsUnit φ).app ((F.rightDerived n).obj M) x)) =
    G.map (homologyMap ψ (n : ℤ))
      (G.map eH.inv (G.map (A.map eI.hom)
        ((sectionsUnit φ).app ((F.rightDerived n).obj M) x))) at hx
  have hA := ConcreteCategory.congr_hom (affineHomologyClass_counit f M I n) x
  change (tilde.adjunction (R := R)).homologyCounitMate (K.sc (n : ℤ))
      (affineHomologyClass f M I n x) =
    (moduleSpecΓFunctor (R := R)).map eI.hom x at hA
  have hu := ConcreteCategory.congr_hom ((sectionsUnit φ).naturality eI.hom) x
  change (sectionsUnit φ).app (K.homology (n : ℤ))
      ((moduleSpecΓFunctor (R := R)).map eI.hom x) =
    G.map (A.map eI.hom) ((sectionsUnit φ).app ((F.rightDerived n).obj M) x) at hu
  change G.map eJ.hom (G.map k ((sectionsUnit φ).app ((F.rightDerived n).obj M) x)) =
    G.map (homologyMap ψ (n : ℤ))
      (G.map eH.inv ((sectionsUnit φ).app (K.homology (n : ℤ))
        ((tilde.adjunction (R := R)).homologyCounitMate (K.sc (n : ℤ))
          (affineHomologyClass f M I n x))))
  rw [hA, hu]
  exact hx

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

section ForwardedCycle

variable [QuasiCompact b] [QuasiSeparated b]

omit [QuasiCompact f] [QuasiSeparated f] [M.IsQuasicoherent]
  [QuasiCompact b] [QuasiSeparated b] in
/-- The actual forwarded cycle is the native affine counit mate of the original pullback cycle. -/
private theorem forwardedCycle_eq
    (c : (affineSectionsComplex f M I).cycles (n : ℤ)) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom
    let β := b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom
    let hs := moduleSectionsBaseChangeScalars a b f φ.hom h.w
    let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let L := ((Scheme.Modules.pushforward b).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
    let ψ := (Scheme.Modules.flatBaseChangeResolutionMapPlus a b f (Spec.map φ) h M I J).hom
    let s := affineSectionCycle f M I n c
    let t := moduleResolutionPullbackSectionCyclesMap a α β φ.hom hs I J n s
    let d := affineSectionCycleInverse b ((Scheme.Modules.pullback a).obj M) J n t
    cyclesForward φ K L ψ (n : ℤ) c =
      (tilde.adjunction (R := S)).cyclesCounitMate (L.sc (n : ℤ)) d := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let β := b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom
  let hs := moduleSectionsBaseChangeScalars a b f φ.hom h.w
  let C := affineSectionsComplex f M I
  let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let L := ((Scheme.Modules.pushforward b).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
  let ψ := (Scheme.Modules.flatBaseChangeResolutionMapPlus a b f (Spec.map φ) h M I J).hom
  let s := affineSectionCycle f M I n c
  let t := moduleResolutionPullbackSectionCyclesMap a α β φ.hom hs I J n s
  let d := affineSectionCycleInverse b ((Scheme.Modules.pullback a).obj M) J n t
  let G := moduleSpecΓFunctor (R := S)
  apply (ModuleCat.mono_iff_injective (G.map (L.iCycles (n : ℤ)))).mp inferInstance
  change G.map (L.iCycles (n : ℤ)) (cyclesForward φ K L ψ (n : ℤ) c) =
    G.map (L.iCycles (n : ℤ)) ((tilde.adjunction (R := S)).cyclesCounitMate (L.sc (n : ℤ)) d)
  rw [cyclesForward_iCycles]
  have hi := ConcreteCategory.congr_hom
    ((tilde.adjunction (R := S)).cyclesCounitMate_iCycles (L.sc (n : ℤ))) d
  change G.map (L.iCycles (n : ℤ))
      ((tilde.adjunction (R := S)).cyclesCounitMate (L.sc (n : ℤ)) d) =
    (affineSectionsComplex b ((Scheme.Modules.pullback a).obj M) J).iCycles (n : ℤ) d at hi
  rw [hi, affineSectionCycleInverse_iCycles]
  change G.map (ψ.f (n : ℤ)) ((sectionsUnit φ).app (K.X (n : ℤ)) (C.iCycles (n : ℤ) c)) =
    ((InjectiveResolution.mapCochainComparison (Scheme.Modules.pullback a) I J).f n).app ⊤
      ((((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
        (I.cochainComplex.X n)).app ⊤) s.val)
  rw [affineSectionCycle_val]
  exact nativeResolutionSections a b f φ h M I J n (C.iCycles (n : ℤ) c)

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
  let N := (Scheme.Modules.pullback a).obj M
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let β := b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom
  let hs := moduleSectionsBaseChangeScalars a b f φ.hom h.w
  let C := affineSectionsComplex f M I
  let D := affineSectionsComplex b N J
  let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let L := ((Scheme.Modules.pushforward b).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
  let ψ := (Scheme.Modules.flatBaseChangeResolutionMapPlus a b f (Spec.map φ) h M I J).hom
  obtain ⟨c, hc⟩ := ((ModuleCat.epi_iff_surjective (C.homologyπ (n : ℤ))).mp inferInstance)
    (affineHomologyClass f M I n x)
  let s := affineSectionCycle f M I n c
  let t := moduleResolutionPullbackSectionCyclesMap a α β φ.hom hs I J n s
  let d := affineSectionCycleInverse b N J n t
  let A := affineHomologyClass b N J n
  let : IsIso A := affineHomologyClass_isIso b N J n
  let y := (asIso A).inv (D.homologyπ (n : ℤ) d)
  have hy := ConcreteCategory.congr_hom (asIso A).inv_hom_id (D.homologyπ (n : ℤ) d)
  change affineHomologyClass b N J n y = D.homologyπ (n : ℤ) d at hy
  have hn := nativeFlat_affineClass a b f φ h M I J n x
  change (moduleSpecΓFunctor (R := S)).map
      (J.isoRightDerivedObjCochain (Scheme.Modules.pushforward b) n).hom
      ((moduleSpecΓFunctor (R := S)).map
        ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f (Spec.map φ) h n).app M)
        ((sectionsUnit φ).app (((Scheme.Modules.pushforward f).rightDerived n).obj M) x)) =
    homologyForward φ K L ψ (n : ℤ) (affineHomologyClass f M I n x) at hn
  rw [← hc, homologyForward_homologyπ, forwardedCycle_eq a b f φ h M I J n] at hn
  have hAy := ConcreteCategory.congr_hom (affineHomologyClass_counit b N J n) y
  change (tilde.adjunction (R := S)).homologyCounitMate (L.sc (n : ℤ))
      (affineHomologyClass b N J n y) =
    (moduleSpecΓFunctor (R := S)).map
      (J.isoRightDerivedObjCochain (Scheme.Modules.pushforward b) n).hom y at hAy
  have hπ := ConcreteCategory.congr_hom
    ((tilde.adjunction (R := S)).homologyCounitMate_homologyπ (L.sc (n : ℤ))) d
  change (tilde.adjunction (R := S)).homologyCounitMate (L.sc (n : ℤ))
      (D.homologyπ (n : ℤ) d) =
    (moduleSpecΓFunctor (R := S)).map (L.homologyπ (n : ℤ))
      ((tilde.adjunction (R := S)).cyclesCounitMate (L.sc (n : ℤ)) d) at hπ
  rw [hy, hπ] at hAy
  have hz : (moduleSpecΓFunctor (R := S)).map
      ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f (Spec.map φ) h n).app M)
      ((sectionsUnit φ).app (((Scheme.Modules.pushforward f).rightDerived n).obj M) x) = y := by
    apply (ModuleCat.mono_iff_injective ((moduleSpecΓFunctor (R := S)).map
      (J.isoRightDerivedObjCochain (Scheme.Modules.pushforward b) n).hom)).mp inferInstance
    exact hn.trans hAy
  rw [hz]
  calc
    moduleHigherDirectImageAffineSectionsLinearEquiv b N J n y =
        moduleResolutionSectionClass Y β J n t := by
      rw [sectionsEquiv_homologyπ b N J n y d hy]
      apply congrArg (moduleResolutionSectionClass Y β J n)
      apply Subtype.ext
      change (affineSectionCycle b N J n d).val = t.val
      rw [affineSectionCycle_val, affineSectionCycleInverse_iCycles]
    _ = moduleCohomologyMapAlong a ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M) n
        (moduleResolutionSectionClass X α I n s) :=
      (moduleResolutionPullbackSectionClass a α β φ.hom hs I J n s).symm
    _ = moduleCohomologyMapAlong a ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M) n
        (moduleHigherDirectImageAffineSectionsLinearEquiv f M I n x) := by
      rw [sectionsEquiv_homologyπ f M I n x c hc.symm]
      rfl

end ForwardedCycle

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
