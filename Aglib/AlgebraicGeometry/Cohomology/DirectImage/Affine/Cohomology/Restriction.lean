/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology.Naturality
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Restriction.Resolution
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Restriction
public import Aglib.AlgebraicGeometry.Modules.Restriction.Unit
public import Aglib.Algebra.Homology.ShortComplex.Adjunction.Counit

/-!
# Original affine higher-image restriction on cohomology

For a qcqs morphism and a quasicoherent coefficient, the original affine
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

universe u w

open CochainComplex HomComplex
open scoped TensorProduct ChangeOfRings

section OpenRestrictionClasses

variable {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
  (p : Y ⟶ X) [IsOpenImmersion p] (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤)) (σ : R →+* S)
  (hσ : p.appTop.hom.comp α = β.comp σ)

/-- The actual geometric unit on global sections, natural in the original module coefficient. -/
private def moduleGlobalSectionsRestrictionMap :
    moduleGlobalSectionsFunctorOfHom X α ⟶ Scheme.Modules.restrictFunctor p ⋙
      moduleGlobalSectionsFunctorOfHom Y β ⋙ ModuleCat.restrictScalars σ where
  app M := moduleGlobalSectionsMapAlong p α β σ hσ
    ((Scheme.Modules.restrictAdjunction p).unit.app M)
  naturality {M N} v := by
    ext x
    change (((Scheme.Modules.restrictAdjunction p).unit.app N).app ⊤)
        (v.app ⊤ x) =
      ((Scheme.Modules.restrictFunctor p).map v).app ⊤
        ((((Scheme.Modules.restrictAdjunction p).unit.app M).app ⊤) x)
    exact congrArg (fun q => q.app ⊤ x)
      ((Scheme.Modules.restrictAdjunction p).unit.naturality v)

private theorem unitHomGlobalSectionsEquiv_restrict (P : X.Modules)
    (k : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ P) :
    Scheme.Modules.unitHomGlobalSectionsEquiv Y ((Scheme.Modules.restrictFunctor p).obj P)
        ((Scheme.Modules.restrictUnitIso p).inv ≫ (Scheme.Modules.restrictFunctor p).map k) =
      (((Scheme.Modules.restrictAdjunction p).unit.app P).app ⊤)
        (Scheme.Modules.unitHomGlobalSectionsEquiv X P k) := by
  have hu := Scheme.Modules.restrictUnitIso_hom_adjoint p
  rw [Adjunction.homEquiv_apply] at hu
  have ht : SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom ≫
      (Scheme.Modules.pushforward p).map
        ((Scheme.Modules.restrictUnitIso p).inv ≫ (Scheme.Modules.restrictFunctor p).map k) =
      k ≫ (Scheme.Modules.restrictAdjunction p).unit.app P := by
    rw [← hu]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
    exact ((Scheme.Modules.restrictAdjunction p).unit.naturality k).symm
  have hv := congrArg
    (fun z : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
        (Scheme.Modules.pushforward p).obj ((Scheme.Modules.restrictFunctor p).obj P) =>
      Scheme.Modules.Hom.app z ⊤ (1 : Γ(X, ⊤))) ht
  change
    (((Scheme.Modules.restrictUnitIso p).inv ≫ (Scheme.Modules.restrictFunctor p).map k).app ⊤)
        (p.appTop (1 : Γ(X, ⊤))) =
      (((Scheme.Modules.restrictAdjunction p).unit.app P).app ⊤)
        (Scheme.Modules.unitHomGlobalSectionsEquiv X P k) at hv
  simpa only [map_one, Scheme.Modules.unitHomGlobalSectionsEquiv_apply] using hv

/-- Native standard derived categories are used for the original resolution comparison. -/
local instance resolutionRestrictionStandard (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

variable {M : X.Modules} (I : InjectiveResolution M)
  (J : InjectiveResolution ((Scheme.Modules.restrictFunctor p).obj M))

/-- The original geometric unit followed by the original resolution comparison, before
scalar extension. The coefficient is the actual native open restriction. -/
private def moduleResolutionRestrictionSectionsMap :
    moduleResolutionSectionComplex X α I ⟶
      ((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj
        (moduleResolutionSectionComplex Y β J) :=
  (NatTrans.mapHomologicalComplex (moduleGlobalSectionsRestrictionMap p α β σ hσ)
      (.up ℤ)).app I.cochainComplex ≫
    ((moduleGlobalSectionsFunctorOfHom Y β ⋙ ModuleCat.restrictScalars σ).mapHomologicalComplex
      (.up ℤ)).map (InjectiveResolution.mapCochainComparison (Scheme.Modules.restrictFunctor p) I J)

/-- The actual section-complex map uses the original module unit and original chosen
resolution comparison in every degree. -/
private theorem moduleResolutionRestrictionSectionsMap_f_apply (i : ℤ)
    (x : (moduleResolutionSectionComplex X α I).X i) :
    (moduleResolutionRestrictionSectionsMap p α β σ hσ I J).f i x =
      ((InjectiveResolution.mapCochainComparison (Scheme.Modules.restrictFunctor p) I J).f i).app ⊤
        ((((Scheme.Modules.restrictAdjunction p).unit.app
          (I.cochainComplex.X i)).app ⊤) x) := rfl

/-- Actual source section cycles map by the original geometric unit and comparison component. -/
private def moduleResolutionRestrictionSectionCyclesMap (n : ℕ) :
    moduleResolutionSectionCycles X α I n →+ moduleResolutionSectionCycles Y β J n where
  toFun s := ⟨(moduleResolutionRestrictionSectionsMap p α β σ hσ I J).f n s.val, by
    let g := moduleResolutionRestrictionSectionsMap p α β σ hσ I J
    have h := congrArg
      (fun q : (moduleResolutionSectionComplex X α I).X n ⟶
          (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj
            (moduleResolutionSectionComplex Y β J)).X ((n : ℤ) + 1) => q s.val)
      (g.comm n ((n : ℤ) + 1))
    change ((moduleResolutionSectionComplex Y β J).d n ((n : ℤ) + 1)) (g.f n s.val) =
      g.f ((n : ℤ) + 1)
        (((moduleResolutionSectionComplex X α I).d n ((n : ℤ) + 1)) s.val) at h
    rw [s.property, map_zero] at h
    exact h⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' s t := Subtype.ext
    (((moduleResolutionRestrictionSectionsMap p α β σ hσ I J).f n).hom.map_add s.val t.val)

private theorem moduleResolutionRestrictionSectionCyclesMap_unitHom (n : ℕ)
    (s : moduleResolutionSectionCycles X α I n) :
    (Scheme.Modules.unitHomGlobalSectionsAddEquiv Y (J.cochainComplex.X n)).symm
        (moduleResolutionRestrictionSectionCyclesMap p α β σ hσ I J n s).val =
      ((Scheme.Modules.restrictUnitIso p).inv ≫ (Scheme.Modules.restrictFunctor p).map
          ((Scheme.Modules.unitHomGlobalSectionsAddEquiv X (I.cochainComplex.X n)).symm s.val)) ≫
        (InjectiveResolution.mapCochainComparison (Scheme.Modules.restrictFunctor p) I J).f n := by
  apply (Scheme.Modules.unitHomGlobalSectionsAddEquiv Y (J.cochainComplex.X n)).injective
  rw [AddEquiv.apply_symm_apply]
  change (moduleResolutionRestrictionSectionCyclesMap p α β σ hσ I J n s).val =
    Scheme.Modules.unitHomGlobalSectionsEquiv Y (J.cochainComplex.X n) (_ ≫ _)
  rw [Scheme.Modules.unitHomGlobalSectionsEquiv_naturality,
    unitHomGlobalSectionsEquiv_restrict]
  change (moduleResolutionRestrictionSectionsMap p α β σ hσ I J).f n s.val =
    ((InjectiveResolution.mapCochainComparison (Scheme.Modules.restrictFunctor p) I J).f n).app ⊤
      ((((Scheme.Modules.restrictAdjunction p).unit.app
          (I.cochainComplex.X n)).app ⊤)
        ((Scheme.Modules.unitHomGlobalSectionsAddEquiv X (I.cochainComplex.X n))
          ((Scheme.Modules.unitHomGlobalSectionsAddEquiv X (I.cochainComplex.X n)).symm s.val)))
  rw [AddEquiv.apply_symm_apply]
  exact moduleResolutionRestrictionSectionsMap_f_apply p α β σ hσ I J n s.val

/-- The actual target section cocycle is the mapped original cocycle followed by the original
resolution comparison, with original unit-module precomposition. -/
private theorem moduleResolutionRestrictionSectionCocycle (n : ℕ)
    (s : moduleResolutionSectionCycles X α I n) :
    moduleResolutionSectionCocycle Y β J n
        (moduleResolutionRestrictionSectionCyclesMap p α β σ hσ I J n s) =
      (InjectiveResolution.mapCochainComparisonCocycle (Scheme.Modules.restrictFunctor p) I J
          (moduleResolutionSectionCocycle X α I n s)).precomp
        ((CochainComplex.singleFunctor Y.Modules 0).map
          (Scheme.Modules.restrictUnitIso p).inv) := by
  let d := InjectiveResolution.mapCochainComparisonCocycle (Scheme.Modules.restrictFunctor p) I J
    (moduleResolutionSectionCocycle X α I n s)
  have hpre : Cochain.fromSingleEquiv (zero_add (n : ℤ))
        (d.precomp ((CochainComplex.singleFunctor Y.Modules 0).map
          (Scheme.Modules.restrictUnitIso p).inv)).1 =
      (Scheme.Modules.restrictUnitIso p).inv ≫
        Cochain.fromSingleEquiv (zero_add (n : ℤ)) d.1 := by
    obtain ⟨r, hr, he⟩ := Cocycle.fromSingleMk_surjective d
      (n : ℤ) (zero_add (n : ℤ)) ((n : ℤ) + 1) rfl
    rw [← he, ← Cocycle.fromSingleMk_precomp]
    simp only [Cocycle.fromSingleMk_coe, Cochain.fromSingleEquiv_fromSingleMk]
  apply Cocycle.ext
  apply (Cochain.fromSingleEquiv (zero_add (n : ℤ))).injective
  change _ = Cochain.fromSingleEquiv (zero_add (n : ℤ))
    (d.precomp ((CochainComplex.singleFunctor Y.Modules 0).map
      (Scheme.Modules.restrictUnitIso p).inv)).1
  rw [hpre]
  dsimp only [d]
  rw [InjectiveResolution.mapCochainComparisonCocycle_fromSingleEquiv]
  simp only [moduleResolutionSectionCocycle, Cocycle.fromSingleMk_coe,
    Cochain.fromSingleEquiv_fromSingleMk]
  simpa only [Category.assoc] using
    moduleResolutionRestrictionSectionCyclesMap_unitHom p α β σ hσ I J n s

/-- The actual mapped section cycle represents exactly the original geometric cohomology
pullback of the original section class. The map uses the actual native open restriction. -/
private theorem moduleResolutionRestrictionSectionClass (n : ℕ)
    (s : moduleResolutionSectionCycles X α I n) :
    moduleCohomologyMapAlong (M := M) (N := (Scheme.Modules.restrictFunctor p).obj M) p
        ((Scheme.Modules.restrictAdjunction p).unit.app M) n
        (moduleResolutionSectionClass X α I n s) =
      moduleResolutionSectionClass Y β J n
        (moduleResolutionRestrictionSectionCyclesMap p α β σ hσ I J n s) := by
  change moduleCohomologyMapAlong p _ n
      (moduleExtCohomologyMap X M n
        (I.extEquivCohomologyClass.symm (.mk (moduleResolutionSectionCocycle X α I n s)))) =
    moduleExtCohomologyMap Y ((Scheme.Modules.restrictFunctor p).obj M) n
      (J.extEquivCohomologyClass.symm (.mk (moduleResolutionSectionCocycle Y β J n
        (moduleResolutionRestrictionSectionCyclesMap p α β σ hσ I J n s))))
  rw [moduleExtCohomologyMap_restrict,
    InjectiveResolution.mapCochainComparisonCocycle_extClass,
    InjectiveResolution.extEquivCohomologyClass_symm_mk_precomp,
    moduleResolutionRestrictionSectionCocycle]


end OpenRestrictionClasses

section AffineCounit

variable (R : CommRingCat.{u}) {ι : Type w} (d : ComplexShape ι)
  (K : HomologicalComplex (Spec R).Modules d) (n : ι)

private def moduleAffineSectionCyclesMap :
    (((moduleSpecΓFunctor.mapHomologicalComplex d).obj K).cycles n) ⟶
      moduleSpecΓFunctor.obj (K.cycles n) :=
  (tilde.adjunction (R := R)).cyclesCounitMate (K.sc n)

private theorem moduleAffineSectionCyclesMap_iCycles :
    moduleAffineSectionCyclesMap R d K n ≫ moduleSpecΓFunctor.map (K.iCycles n) =
      ((moduleSpecΓFunctor.mapHomologicalComplex d).obj K).iCycles n :=
  (tilde.adjunction (R := R)).cyclesCounitMate_iCycles (K.sc n)

private theorem moduleAffineCounitHomologyMap_homologyπ
    [QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit R d K)] :
    let C := (moduleSpecΓFunctor.mapHomologicalComplex d).obj K
    C.homologyπ n ≫ (tilde.adjunction (R := R)).unit.app (C.homology n) ≫
        moduleSpecΓFunctor.map
          (Scheme.Modules.Complex.tildeGlobalSectionsHomologyIso R d K n).hom =
      moduleAffineSectionCyclesMap R d K n ≫ moduleSpecΓFunctor.map (K.homologyπ n) := by
  change ((K.sc n).map moduleSpecΓFunctor).homologyπ ≫
      (tilde.adjunction (R := R)).homologyCounitMate (K.sc n) =
    (tilde.adjunction (R := R)).cyclesCounitMate (K.sc n) ≫
      moduleSpecΓFunctor.map (K.sc n).homologyπ
  exact (tilde.adjunction (R := R)).homologyCounitMate_homologyπ (K.sc n)


end AffineCounit

section AffineClasses



private def affineCounitUnit (R : CommRingCat.{u})
    (K : CochainComplex (Spec R).Modules ℤ) (n : ℕ) :
    ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K).homology (n : ℤ) ⟶
      moduleSpecΓFunctor.obj (K.homology (n : ℤ)) :=
  (tilde.adjunction (R := R)).homologyCounitMate (K.sc (n : ℤ))

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
  (M : X.Modules) [M.IsQuasicoherent] (I : InjectiveResolution M) (n : ℕ)

private def affineHomologyClass :
    moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward f).rightDerived n).obj M) ⟶
      ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj
        (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj
          I.cochainComplex)).homology (n : ℤ) :=
  moduleSpecΓFunctor.map (moduleHigherDirectImageAffineIso f M I n).hom ≫
    (tilde.toTildeΓNatIso (R := CommRingCat.of R)).inv.app
      (((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj
        (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj
          I.cochainComplex)).homology (n : ℤ))

private theorem affineHomologyClass_isIso : IsIso (affineHomologyClass f M I n) := by
  dsimp only [affineHomologyClass]
  infer_instance

private theorem affineHomologyClass_counit :
    let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    affineHomologyClass f M I n ≫ affineCounitUnit (CommRingCat.of R) K n =
      moduleSpecΓFunctor.map
        (I.isoRightDerivedObjCochain (Scheme.Modules.pushforward f) n).hom := by
  let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let C := (moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K
  let : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
      (CommRingCat.of R) (.up ℤ) K) := moduleResolutionPushforwardTildeCounit_quasiIso f M I
  change moduleSpecΓFunctor.map (moduleHigherDirectImageAffineIso f M I n).hom ≫
      (tilde.toTildeΓNatIso (R := CommRingCat.of R)).inv.app (C.homology (n : ℤ)) ≫
      (tilde.toTildeΓNatIso (R := CommRingCat.of R)).hom.app (C.homology (n : ℤ)) ≫
      moduleSpecΓFunctor.map
        (Scheme.Modules.Complex.tildeGlobalSectionsHomologyIso
          (CommRingCat.of R) (.up ℤ) K (n : ℤ)).hom = _
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp]
  exact congrArg moduleSpecΓFunctor.map
    (moduleHigherDirectImageAffineIso_hom_comp f M I n)

private theorem sectionsEquiv_eq_resolutionClass
    (x : moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward f).rightDerived n).obj M)) :
    moduleHigherDirectImageAffineSectionsLinearEquiv f M I n x =
      moduleResolutionSectionsCohomologyLinearEquiv X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) I n
        (homologyMap (moduleSpecPushforwardGlobalSectionsComplexIso
          f (.up ℤ) I.cochainComplex).hom (n : ℤ) (affineHomologyClass f M I n x)) := rfl




private abbrev affineSectionsComplex : CochainComplex (ModuleCat.{u} R) ℤ :=
  (moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj
    (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)

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


private def affineSectionCycle
    (c : (affineSectionsComplex f M I).cycles (n : ℤ)) :
    moduleResolutionSectionCycles X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) I n :=
  (moduleResolutionSectionCyclesIso X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) I n).hom
      (cyclesMap (moduleSpecPushforwardGlobalSectionsComplexIso
        f (.up ℤ) I.cochainComplex).hom (n : ℤ) c)

omit [QuasiCompact f] [QuasiSeparated f] [M.IsQuasicoherent] in
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

private def affineSectionCycleInverse
    (s : moduleResolutionSectionCycles X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) I n) :
    (affineSectionsComplex f M I).cycles (n : ℤ) :=
  cyclesMap (moduleSpecPushforwardGlobalSectionsComplexIso
      f (.up ℤ) I.cochainComplex).inv (n : ℤ)
    ((moduleResolutionSectionCyclesIso X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) I n).inv s)

omit [QuasiCompact f] [QuasiSeparated f] [M.IsQuasicoherent] in
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

private def cyclesForward
    (c : ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K).cycles n) :
    (moduleSpecΓFunctor (R := S)).obj (L.cycles n) :=
  (moduleSpecΓFunctor (R := S)).map (HomologicalComplex.cyclesMap ψ n)
    ((moduleSpecΓFunctor (R := S)).map
      (((K.sc n).mapCyclesIso (Scheme.Modules.restrictFunctor (Spec.map φ))).inv)
      ((sectionsUnit φ).app (K.cycles n)
        ((tilde.adjunction (R := R)).cyclesCounitMate (K.sc n) c)))

private theorem cyclesForward_iCycles
    (c : ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K).cycles n) :
    (moduleSpecΓFunctor (R := S)).map (L.iCycles n) (cyclesForward φ K L ψ n c) =
      (moduleSpecΓFunctor (R := S)).map (ψ.f n)
        ((sectionsUnit φ).app (K.X n)
          (((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K).iCycles n c)) := by
  let G := moduleSpecΓFunctor (R := S)
  let J := Scheme.Modules.restrictFunctor (Spec.map φ)
  let C := (moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K
  let T := (J.mapHomologicalComplex (.up ℤ)).obj K
  let e := (K.sc n).mapCyclesIso J
  let s := (tilde.adjunction (R := R)).cyclesCounitMate (K.sc n) c
  let z : G.obj (J.obj (K.cycles n)) := (sectionsUnit φ).app (K.cycles n) s
  let w : G.obj (T.cycles n) := G.map e.inv z
  have hh := congrArg G.map (HomologicalComplex.cyclesMap_i ψ n)
  simp only [Functor.map_comp] at hh
  have hψ := ConcreteCategory.congr_hom hh w
  change G.map (L.iCycles n) (G.map (HomologicalComplex.cyclesMap ψ n) w) =
    G.map (ψ.f n) (G.map (T.iCycles n) w) at hψ
  have he := congrArg G.map (ShortComplex.mapCyclesIso_inv_iCycles J (K.sc n))
  simp only [Functor.map_comp] at he
  have hex := ConcreteCategory.congr_hom he z
  change G.map (T.iCycles n) (G.map e.inv z) = G.map (J.map (K.iCycles n)) z at hex
  have hu := ConcreteCategory.congr_hom ((sectionsUnit φ).naturality (K.iCycles n)) s
  change (sectionsUnit φ).app (K.X n) ((moduleSpecΓFunctor (R := R)).map (K.iCycles n) s) =
    G.map (J.map (K.iCycles n)) z at hu
  have hc := ConcreteCategory.congr_hom
    ((tilde.adjunction (R := R)).cyclesCounitMate_iCycles (K.sc n)) c
  change (moduleSpecΓFunctor (R := R)).map (K.iCycles n) s = C.iCycles n c at hc
  change G.map (L.iCycles n) (G.map (HomologicalComplex.cyclesMap ψ n) w) = _
  rw [hψ, hex, ← hu, hc]




private def homologyForward
    (x : ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K).homology n) :
    (moduleSpecΓFunctor (R := S)).obj (L.homology n) :=
  (moduleSpecΓFunctor (R := S)).map (HomologicalComplex.homologyMap ψ n)
    ((moduleSpecΓFunctor (R := S)).map
      (((K.sc n).mapHomologyIso (Scheme.Modules.restrictFunctor (Spec.map φ))).inv)
      ((sectionsUnit φ).app (K.homology n)
        ((tilde.adjunction (R := R)).homologyCounitMate (K.sc n) x)))

private theorem homologyForward_homologyπ
    (c : ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K).cycles n) :
    homologyForward φ K L ψ n
        (((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K).homologyπ n c) =
      (moduleSpecΓFunctor (R := S)).map (L.homologyπ n) (cyclesForward φ K L ψ n c) := by
  let G := moduleSpecΓFunctor (R := S)
  let J := Scheme.Modules.restrictFunctor (Spec.map φ)
  let C := (moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K
  let T := (J.mapHomologicalComplex (.up ℤ)).obj K
  let eH := (K.sc n).mapHomologyIso J
  let eC := (K.sc n).mapCyclesIso J
  let s := (tilde.adjunction (R := R)).cyclesCounitMate (K.sc n) c
  let z : G.obj (J.obj (K.cycles n)) := (sectionsUnit φ).app (K.cycles n) s
  let w : G.obj (T.cycles n) := G.map eC.inv z
  have hc := ConcreteCategory.congr_hom
    ((tilde.adjunction (R := R)).homologyCounitMate_homologyπ (K.sc n)) c
  change (tilde.adjunction (R := R)).homologyCounitMate (K.sc n) (C.homologyπ n c) =
    (moduleSpecΓFunctor (R := R)).map (K.homologyπ n) s at hc
  have hu := ConcreteCategory.congr_hom ((sectionsUnit φ).naturality (K.homologyπ n)) s
  change (sectionsUnit φ).app (K.homology n)
      ((moduleSpecΓFunctor (R := R)).map (K.homologyπ n) s) =
    G.map (J.map (K.homologyπ n)) z at hu
  have he := congrArg G.map (ShortComplex.map_homologyπ_mapHomologyIso_inv J (K.sc n))
  simp only [Functor.map_comp] at he
  have hex := ConcreteCategory.congr_hom he z
  change G.map eH.inv (G.map (J.map (K.homologyπ n)) z) = G.map (T.homologyπ n) w at hex
  have hh := congrArg G.map (HomologicalComplex.homologyπ_naturality ψ n)
  simp only [Functor.map_comp] at hh
  have hψ := ConcreteCategory.congr_hom hh w
  change G.map (HomologicalComplex.homologyMap ψ n) (G.map (T.homologyπ n) w) =
    G.map (L.homologyπ n) (G.map (HomologicalComplex.cyclesMap ψ n) w) at hψ
  change G.map (HomologicalComplex.homologyMap ψ n)
      (G.map eH.inv ((sectionsUnit φ).app (K.homology n)
        ((tilde.adjunction (R := R)).homologyCounitMate (K.sc n) (C.homologyπ n c)))) = _
  rw [hc, hu, hex, hψ]
  rfl


end Forward


section NativeOpen

local instance nativeAffineStandard (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

variable {R S : CommRingCat.{u}} {X Y : Scheme.{u}}
  (a : Y ⟶ X) (b : Y ⟶ Spec S) (f : X ⟶ Spec R)
  [QuasiCompact f] [QuasiSeparated f] (φ : R ⟶ S)
  [IsOpenImmersion a] [IsOpenImmersion (Spec.map φ)]
  (h : IsPullback a b f (Spec.map φ)) (M : X.Modules) [M.IsQuasicoherent]
  (I : InjectiveResolution M)
  (J : InjectiveResolution ((Scheme.Modules.restrictFunctor a).obj M)) (n : ℕ)

private theorem nativeOpen_affineClass
    (x : (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived n).obj M)) :
    let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let L := ((Scheme.Modules.pushforward b).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
    let ψ := (Scheme.Modules.openBaseChangeResolutionMapPlus a b f (Spec.map φ) h M I J).hom
    (moduleSpecΓFunctor (R := S)).map
        (J.isoRightDerivedObjCochain (Scheme.Modules.pushforward b) n).hom
        ((moduleSpecΓFunctor (R := S)).map
          ((Scheme.Modules.higherDirectImageOpenRestrictionIso a b f (Spec.map φ) h n).hom.app M)
          ((sectionsUnit φ).app (((Scheme.Modules.pushforward f).rightDerived n).obj M) x)) =
      homologyForward φ K L ψ (n : ℤ) (affineHomologyClass f M I n x) := by
  let F := Scheme.Modules.pushforward f
  let B := Scheme.Modules.pushforward b
  let A := Scheme.Modules.restrictFunctor (Spec.map φ)
  let G := moduleSpecΓFunctor (R := S)
  let K := (F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let L := (B.mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
  let ψ := (Scheme.Modules.openBaseChangeResolutionMapPlus a b f (Spec.map φ) h M I J).hom
  let eI := I.isoRightDerivedObjCochain F n
  let eJ := J.isoRightDerivedObjCochain B n
  let eH := (K.sc (n : ℤ)).mapHomologyIso A
  let k := (Scheme.Modules.higherDirectImageOpenRestrictionIso a b f (Spec.map φ) h n).hom.app M
  have hk := congrArg (fun t => t ≫ eJ.hom)
    (Scheme.Modules.higherDirectImageOpenRestrictionIso_app_resolution
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



omit [QuasiCompact f] [QuasiSeparated f] [M.IsQuasicoherent] in
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


section ForwardedCycle

variable [QuasiCompact b] [QuasiSeparated b]

omit [QuasiCompact f] [QuasiSeparated f] [M.IsQuasicoherent]
  [QuasiCompact b] [QuasiSeparated b] in
private theorem forwardedCycle_eq
    (c : (affineSectionsComplex f M I).cycles (n : ℤ)) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom
    let β := b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom
    let hs := moduleSectionsBaseChangeScalars a b f φ.hom h.w
    let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let L := ((Scheme.Modules.pushforward b).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
    let ψ := (Scheme.Modules.openBaseChangeResolutionMapPlus a b f (Spec.map φ) h M I J).hom
    let s := affineSectionCycle f M I n c
    let t := moduleResolutionRestrictionSectionCyclesMap a α β φ.hom hs I J n s
    let d := affineSectionCycleInverse b ((Scheme.Modules.restrictFunctor a).obj M) J n t
    cyclesForward φ K L ψ (n : ℤ) c =
      (tilde.adjunction (R := S)).cyclesCounitMate (L.sc (n : ℤ)) d := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let β := b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom
  let hs := moduleSectionsBaseChangeScalars a b f φ.hom h.w
  let C := affineSectionsComplex f M I
  let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let L := ((Scheme.Modules.pushforward b).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
  let ψ := (Scheme.Modules.openBaseChangeResolutionMapPlus a b f (Spec.map φ) h M I J).hom
  let s := affineSectionCycle f M I n c
  let t := moduleResolutionRestrictionSectionCyclesMap a α β φ.hom hs I J n s
  let d := affineSectionCycleInverse b ((Scheme.Modules.restrictFunctor a).obj M) J n t
  let G := moduleSpecΓFunctor (R := S)
  apply (ModuleCat.mono_iff_injective (G.map (L.iCycles (n : ℤ)))).mp inferInstance
  change G.map (L.iCycles (n : ℤ)) (cyclesForward φ K L ψ (n : ℤ) c) =
    G.map (L.iCycles (n : ℤ)) ((tilde.adjunction (R := S)).cyclesCounitMate (L.sc (n : ℤ)) d)
  rw [cyclesForward_iCycles]
  have hi := ConcreteCategory.congr_hom
    ((tilde.adjunction (R := S)).cyclesCounitMate_iCycles (L.sc (n : ℤ))) d
  change G.map (L.iCycles (n : ℤ))
      ((tilde.adjunction (R := S)).cyclesCounitMate (L.sc (n : ℤ)) d) =
    (affineSectionsComplex b ((Scheme.Modules.restrictFunctor a).obj M) J).iCycles (n : ℤ) d at hi
  rw [hi, affineSectionCycleInverse_iCycles]
  change G.map (ψ.f (n : ℤ)) ((sectionsUnit φ).app (K.X (n : ℤ)) (C.iCycles (n : ℤ) c)) =
    ((InjectiveResolution.mapCochainComparison (Scheme.Modules.restrictFunctor a) I J).f n).app ⊤
      ((((Scheme.Modules.restrictAdjunction a).unit.app (I.cochainComplex.X n)).app ⊤) s.val)
  rw [affineSectionCycle_val]
  exact nativeResolutionSections a b f φ h M I J n (C.iCycles (n : ℤ) c)

private theorem sectionsEquiv_openRestriction
    (x : (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived n).obj M)) :
    moduleHigherDirectImageAffineSectionsLinearEquiv b
        ((Scheme.Modules.restrictFunctor a).obj M) J n
        ((moduleSpecΓFunctor (R := S)).map
          ((Scheme.Modules.higherDirectImageOpenRestrictionIso a b f (Spec.map φ) h n).hom.app M)
          ((sectionsUnit φ).app (((Scheme.Modules.pushforward f).rightDerived n).obj M) x)) =
      moduleCohomologyMapAlong a ((Scheme.Modules.restrictAdjunction a).unit.app M) n
        (moduleHigherDirectImageAffineSectionsLinearEquiv f M I n x) := by
  let N := (Scheme.Modules.restrictFunctor a).obj M
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let β := b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom
  let hs := moduleSectionsBaseChangeScalars a b f φ.hom h.w
  let C := affineSectionsComplex f M I
  let D := affineSectionsComplex b N J
  let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let L := ((Scheme.Modules.pushforward b).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
  let ψ := (Scheme.Modules.openBaseChangeResolutionMapPlus a b f (Spec.map φ) h M I J).hom
  obtain ⟨c, hc⟩ := ((ModuleCat.epi_iff_surjective (C.homologyπ (n : ℤ))).mp inferInstance)
    (affineHomologyClass f M I n x)
  let s := affineSectionCycle f M I n c
  let t := moduleResolutionRestrictionSectionCyclesMap a α β φ.hom hs I J n s
  let d := affineSectionCycleInverse b N J n t
  let A := affineHomologyClass b N J n
  let : IsIso A := affineHomologyClass_isIso b N J n
  let y := (asIso A).inv (D.homologyπ (n : ℤ) d)
  have hy := ConcreteCategory.congr_hom (asIso A).inv_hom_id (D.homologyπ (n : ℤ) d)
  change affineHomologyClass b N J n y = D.homologyπ (n : ℤ) d at hy
  have hn := nativeOpen_affineClass a b f φ h M I J n x
  change (moduleSpecΓFunctor (R := S)).map
      (J.isoRightDerivedObjCochain (Scheme.Modules.pushforward b) n).hom
      ((moduleSpecΓFunctor (R := S)).map
        ((Scheme.Modules.higherDirectImageOpenRestrictionIso a b f (Spec.map φ) h n).hom.app M)
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
      ((Scheme.Modules.higherDirectImageOpenRestrictionIso a b f (Spec.map φ) h n).hom.app M)
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
    _ = moduleCohomologyMapAlong a ((Scheme.Modules.restrictAdjunction a).unit.app M) n
        (moduleResolutionSectionClass X α I n s) :=
      (moduleResolutionRestrictionSectionClass a α β φ.hom hs I J n s).symm
    _ = moduleCohomologyMapAlong a ((Scheme.Modules.restrictAdjunction a).unit.app M) n
        (moduleHigherDirectImageAffineSectionsLinearEquiv f M I n x) := by
      rw [sectionsEquiv_homologyπ f M I n x c hc.symm]
      rfl

end ForwardedCycle

end NativeOpen



-- The native unit and its scalar-forgetting component have deeply nested functor types.
set_option maxRecDepth 2000 in
/-- On an actual affine cartesian open square, the original higher-image comparison
becomes the original geometric cohomology map under the original affine section
comparisons. Target qcqs follows from the supplied cartesian square. -/
theorem moduleHigherDirectImageAffineSectionsLinearEquiv_openRestriction
    {R S : CommRingCat.{u}} {X Y : Scheme.{u}}
    (a : Y ⟶ X) (b : Y ⟶ Spec S) (f : X ⟶ Spec R)
    [QuasiCompact f] [QuasiSeparated f] (φ : R ⟶ S)
    [IsOpenImmersion a] [IsOpenImmersion (Spec.map φ)]
    (h : IsPullback a b f (Spec.map φ)) (M : X.Modules) [M.IsQuasicoherent]
    (I : InjectiveResolution M)
    (J : InjectiveResolution ((Scheme.Modules.restrictFunctor a).obj M)) (n : ℕ)
    (x : (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived n).obj M)) :
    letI : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
    letI : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
    moduleHigherDirectImageAffineSectionsLinearEquiv b
        ((Scheme.Modules.restrictFunctor a).obj M) J n
        ((moduleSpecΓFunctor (R := S)).map
          ((Scheme.Modules.higherDirectImageOpenRestrictionIso a b f (Spec.map φ) h n).hom.app M)
          ((((Scheme.Modules.restrictAdjunction (Spec.map φ)).unit.app
            (((Scheme.Modules.pushforward f).rightDerived n).obj M)).app ⊤) x)) =
      moduleCohomologyMapAlong a ((Scheme.Modules.restrictAdjunction a).unit.app M) n
        (moduleHigherDirectImageAffineSectionsLinearEquiv f M I n x) := by
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  exact sectionsEquiv_openRestriction a b f φ h M I J n x

end AlgebraicGeometry.Scheme.Cohomology
