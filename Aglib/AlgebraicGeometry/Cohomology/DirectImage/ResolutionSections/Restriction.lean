/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Restriction
public import Aglib.AlgebraicGeometry.Modules.Restriction.Unit

/-!
# Actual open restriction on original resolution sections

The geometric restriction unit and original resolution comparison give the
actual section-complex map. Its homology map uses the exact restriction of
scalars, and its classes are the original geometric cohomology pullback.
The unit-module comparison remains the original `restrictUnitIso`.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open AlgebraicGeometry CochainComplex HomComplex

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
  (p : Y ⟶ X) [IsOpenImmersion p] (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤)) (σ : R →+* S)
  (hσ : p.appTop.hom.comp α = β.comp σ)

/-- The actual geometric unit on global sections, natural in the original module coefficient. -/
def moduleGlobalSectionsRestrictionMap :
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

theorem unitHomGlobalSectionsEquiv_restrict (P : X.Modules)
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
def moduleResolutionRestrictionSectionsMap :
    moduleResolutionSectionComplex X α I ⟶
      ((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj
        (moduleResolutionSectionComplex Y β J) :=
  (NatTrans.mapHomologicalComplex (moduleGlobalSectionsRestrictionMap p α β σ hσ)
      (.up ℤ)).app I.cochainComplex ≫
    ((moduleGlobalSectionsFunctorOfHom Y β ⋙ ModuleCat.restrictScalars σ).mapHomologicalComplex
      (.up ℤ)).map (InjectiveResolution.mapCochainComparison (Scheme.Modules.restrictFunctor p) I J)

/-- The actual section-complex map uses the original module unit and original chosen
resolution comparison in every degree. -/
theorem moduleResolutionRestrictionSectionsMap_f_apply (i : ℤ)
    (x : (moduleResolutionSectionComplex X α I).X i) :
    (moduleResolutionRestrictionSectionsMap p α β σ hσ I J).f i x =
      ((InjectiveResolution.mapCochainComparison (Scheme.Modules.restrictFunctor p) I J).f i).app ⊤
        ((((Scheme.Modules.restrictAdjunction p).unit.app
          (I.cochainComplex.X i)).app ⊤) x) := rfl

/-- Actual source section cycles map by the original geometric unit and comparison component. -/
def moduleResolutionRestrictionSectionCyclesMap (n : ℕ) :
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

theorem moduleResolutionRestrictionSectionCyclesMap_unitHom (n : ℕ)
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
theorem moduleResolutionRestrictionSectionCocycle (n : ℕ)
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
theorem moduleResolutionRestrictionSectionClass (n : ℕ)
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


/-- Homology of the original restriction section map, with the original exact
restriction-of-scalars comparison. -/
def moduleResolutionRestrictionSectionsHomologyMap (n : ℤ) :
    (moduleResolutionSectionComplex X α I).homology n ⟶
      (ModuleCat.restrictScalars σ).obj ((moduleResolutionSectionComplex Y β J).homology n) :=
  homologyMap (moduleResolutionRestrictionSectionsMap p α β σ hσ I J) n ≫
    (((moduleResolutionSectionComplex Y β J).sc n).mapHomologyIso
      (ModuleCat.restrictScalars σ)).hom

/-- The corresponding map of the original cycle objects. -/
def moduleResolutionRestrictionHomologyCyclesMap (n : ℤ) :
    (moduleResolutionSectionComplex X α I).cycles n ⟶
      (ModuleCat.restrictScalars σ).obj ((moduleResolutionSectionComplex Y β J).cycles n) :=
  cyclesMap (moduleResolutionRestrictionSectionsMap p α β σ hσ I J) n ≫
    (((moduleResolutionSectionComplex Y β J).sc n).mapCyclesIso
      (ModuleCat.restrictScalars σ)).hom

/-- The homology cycle map retains the actual degree component. -/
theorem moduleResolutionRestrictionHomologyCyclesMap_iCycles (n : ℤ) :
    moduleResolutionRestrictionHomologyCyclesMap p α β σ hσ I J n ≫
        (ModuleCat.restrictScalars σ).map
          ((moduleResolutionSectionComplex Y β J).iCycles n) =
      (moduleResolutionSectionComplex X α I).iCycles n ≫
        (moduleResolutionRestrictionSectionsMap p α β σ hσ I J).f n := by
  let q := moduleResolutionRestrictionSectionsMap p α β σ hσ I J
  have h := congrArg (fun z => cyclesMap q n ≫ z)
    (ShortComplex.mapCyclesIso_hom_iCycles ((moduleResolutionSectionComplex Y β J).sc n)
      (ModuleCat.restrictScalars σ))
  exact (Category.assoc _ _ _).trans (h.trans (HomologicalComplex.cyclesMap_i q n))

/-- The actual cycle projection computes the whole restriction homology map. -/
theorem moduleResolutionRestrictionSectionsHomologyMap_homologyπ (n : ℤ)
    (c : (moduleResolutionSectionComplex X α I).cycles n) :
    moduleResolutionRestrictionSectionsHomologyMap p α β σ hσ I J n
        ((moduleResolutionSectionComplex X α I).homologyπ n c) =
      (moduleResolutionSectionComplex Y β J).homologyπ n
        (moduleResolutionRestrictionHomologyCyclesMap p α β σ hσ I J n c) := by
  have h : (moduleResolutionSectionComplex X α I).homologyπ n ≫
        moduleResolutionRestrictionSectionsHomologyMap p α β σ hσ I J n =
      moduleResolutionRestrictionHomologyCyclesMap p α β σ hσ I J n ≫
        (ModuleCat.restrictScalars σ).map
          ((moduleResolutionSectionComplex Y β J).homologyπ n) := by
    dsimp only [moduleResolutionRestrictionSectionsHomologyMap,
      moduleResolutionRestrictionHomologyCyclesMap]
    rw [HomologicalComplex.homologyπ_naturality_assoc]
    have hπ := congrArg
      (fun z => cyclesMap (moduleResolutionRestrictionSectionsMap p α β σ hσ I J) n ≫ z)
      (ShortComplex.homologyπ_mapHomologyIso_hom (ModuleCat.restrictScalars σ)
        ((moduleResolutionSectionComplex Y β J).sc n))
    exact hπ.trans (Category.assoc _ _ _).symm
  exact ConcreteCategory.congr_hom h c

/-- The actual homology map is the original geometric cohomology restriction under
both original resolution-section comparisons. No affine or quasi-coherence hypothesis
is required. -/
theorem moduleResolutionRestrictionSectionsHomologyMap_cohomology (n : ℕ)
    (x : (moduleResolutionSectionComplex X α I).homology (n : ℤ)) :
    moduleResolutionSectionsCohomologyLinearEquiv Y β J n
        (moduleResolutionRestrictionSectionsHomologyMap p α β σ hσ I J n x) =
      moduleCohomologyMapAlong (M := M) (N := (Scheme.Modules.restrictFunctor p).obj M) p
        ((Scheme.Modules.restrictAdjunction p).unit.app M) n
        (moduleResolutionSectionsCohomologyLinearEquiv X α I n x) := by
  obtain ⟨c, rfl⟩ := ((ModuleCat.epi_iff_surjective
    ((moduleResolutionSectionComplex X α I).homologyπ (n : ℤ))).mp inferInstance) x
  rw [moduleResolutionRestrictionSectionsHomologyMap_homologyπ p α β σ hσ I J,
    moduleResolutionSectionsCohomologyLinearEquiv_homologyπ Y β J,
    moduleResolutionSectionsCohomologyLinearEquiv_homologyπ X α I,
    moduleResolutionRestrictionSectionClass p α β σ hσ I J]
  apply congrArg (moduleResolutionSectionClass Y β J n)
  apply Subtype.ext
  rw [moduleResolutionSectionCyclesIso_hom_val]
  change (moduleResolutionSectionComplex Y β J).iCycles n
      (moduleResolutionRestrictionHomologyCyclesMap p α β σ hσ I J n c) =
    (moduleResolutionRestrictionSectionsMap p α β σ hσ I J).f n
      ((moduleResolutionSectionCyclesIso X α I n).hom c).val
  rw [moduleResolutionSectionCyclesIso_hom_val]
  exact ConcreteCategory.congr_hom
    (moduleResolutionRestrictionHomologyCyclesMap_iCycles p α β σ hσ I J n) c

end AlgebraicGeometry.Scheme.Cohomology
