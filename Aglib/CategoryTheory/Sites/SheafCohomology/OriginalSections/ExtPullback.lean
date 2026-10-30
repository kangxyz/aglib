/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.OriginalSections.DerivedPullback
public import Aglib.CategoryTheory.Abelian.Ext.SourceTransfer
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.CocycleComparison

/-! # Original Ext and actual derived section pullback

The original integer-source map and the ordinary image-unit map agree on every
supplied resolution. The whole comparison is proved from those same augmented
lifts and cocycles, then identifies the actual canonical derived-unit map.
Source and target Ext worlds remain independent of the section-value world.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex.HomComplex

namespace CategoryTheory.Adjunction

universe uC uD s w w' dC dD dV

/-- The homology class of an explicit section cocycle, using the native
cycle-object and homology projection. -/
def originalSectionCycleClass (K : CochainComplex AddCommGrpCat.{s} ℤ)
    (n : ℤ) (x : K.X n) (hx : K.d n (n + 1) x = 0) : K.homology n :=
  K.homologyπ n ((K.sc n).abCyclesIso.inv ⟨x, by
    change K.d n ((ComplexShape.up ℤ).next n) x = 0
    rw [CochainComplex.next ℤ n]
    exact hx⟩)

private theorem originalSectionCycleClass_map
    {K L : CochainComplex AddCommGrpCat.{s} ℤ} (φ : K ⟶ L)
    (n : ℤ) (x : K.X n) (hx : K.d n (n + 1) x = 0) :
    homologyMap φ n (originalSectionCycleClass K n x hx) =
      originalSectionCycleClass L n (φ.f n x) (by
        rw [← ConcreteCategory.comp_apply, φ.comm, ConcreteCategory.comp_apply, hx]
        exact map_zero _) := by
  exact HomologicalComplex.addCommGrpCycleClass_map φ n x hx

variable {C : Type uC} [Category.{s} C] [Abelian C] [EnoughInjectives C]
  {D : Type uD} [Category.{s} D] [Abelian D] [EnoughInjectives D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The actual section-complex map from the supplied exact-functor resolution lift. -/
def resolutionSectionsPullback
    (imageAdj : F ⊣ G) (Γ : C ⥤ AddCommGrpCat.{s}) {Δ : D ⥤ AddCommGrpCat.{s}}
    [Γ.Additive] [Δ.Additive] (e : G ⋙ Γ ≅ Δ)
    {L : C} (I : InjectiveResolution L) (J : InjectiveResolution (F.obj L))
    (φ : InjectiveResolution.ExactFunctor.mappedResolution F I ⟶ J.cocomplex) :
    (Γ.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex ⟶
      (Δ.mapHomologicalComplex (.up ℤ)).obj J.cochainComplex :=
  (NatTrans.mapHomologicalComplex (unitSectionsNatTrans imageAdj Γ e) (.up ℤ)).app
      I.cochainComplex ≫
    (Δ.mapHomologicalComplex (.up ℤ)).map
      (InjectiveResolution.ExactFunctor.extendedLift F I J φ)

/-- Homology of the same supplied section-complex map. -/
def rightDerivedSectionsPullbackOfLift
    (imageAdj : F ⊣ G) (Γ : C ⥤ AddCommGrpCat.{s}) {Δ : D ⥤ AddCommGrpCat.{s}}
    [Γ.Additive] [Δ.Additive] (e : G ⋙ Γ ≅ Δ)
    {L : C} (I : InjectiveResolution L) (J : InjectiveResolution (F.obj L))
    (φ : InjectiveResolution.ExactFunctor.mappedResolution F I ⟶ J.cocomplex) (n : ℕ) :
    (Γ.rightDerived n).obj L ⟶ (Δ.rightDerived n).obj (F.obj L) :=
  (I.isoRightDerivedObjCochain Γ n).hom ≫
    homologyMap (resolutionSectionsPullback imageAdj Γ e I J φ) (n : ℤ) ≫
    (J.isoRightDerivedObjCochain Δ n).inv

variable
  {K : AddCommGrpCat.{s} ⥤ C} {Γ : C ⥤ AddCommGrpCat.{s}}
  {K' : AddCommGrpCat.{s} ⥤ D} {Δ : D ⥤ AddCommGrpCat.{s}}
  [K.Additive] [K'.Additive] [Γ.Additive] [Δ.Additive]
  (constantAdj : K ⊣ Γ) (imageAdj : F ⊣ G) (constantAdj' : K' ⊣ Δ)
  (e : G ⋙ Γ ≅ Δ) (c : K ⋙ F ≅ K')
  (hc : c = leftAdjointCompIso constantAdj imageAdj constantAdj' e)
  [HasExt.{w} C] [HasExt.{w'} D]

omit [EnoughInjectives C] [EnoughInjectives D] [K.Additive] [K'.Additive] in
/-- The actual exact-functor Ext map retains the original transported resolution cycle. -/
theorem integerSourcePullback_extMk
    {L : C} (I : InjectiveResolution L) (J : InjectiveResolution (F.obj L))
    (φ : InjectiveResolution.ExactFunctor.mappedResolution F I ⟶ J.cocomplex)
    (hφ : F.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) (n : ℕ)
    (a : K.obj (AddCommGrpCat.of (ULift.{s} ℤ)) ⟶ I.cocomplex.X n)
    (ha : a ≫ I.cocomplex.d n (n + 1) = 0) :
    F.extPrecompMap (c.app (AddCommGrpCat.of (ULift.{s} ℤ))).inv L n
        (I.extMk a (n + 1) rfl ha) =
      J.extMk ((c.app (AddCommGrpCat.of (ULift.{s} ℤ))).inv ≫ F.map a ≫ φ.f n)
        (n + 1) rfl (by
          simpa only [Category.assoc, comp_zero] using
            congrArg (fun z => (c.app (AddCommGrpCat.of (ULift.{s} ℤ))).inv ≫ z)
              (InjectiveResolution.ExactFunctor.mappedCycle_comp_d φ n a ha)) := by
  have h := InjectiveResolution.ExactFunctor.mk₀_comp_extMk_mapExactFunctor_comp_mk₀
    F I J (𝟙 _) φ (by simpa only [Category.id_comp] using hφ) a ha
    (c.app (AddCommGrpCat.of (ULift.{s} ℤ))).inv
  change (Abelian.Ext.mk₀ _).comp
      ((I.extMk a (n + 1) rfl ha).mapExactFunctor F) (zero_add n) = _
  simpa only [Abelian.Ext.comp_mk₀_id] using h

/-- The actual Gamma comparison on an integer-resolution cocycle, through the
accepted native NT resolution comparison and the actual cycle class. -/
theorem originalSectionsExtEquivOfResolution_cocycle
    {L : C} (I : InjectiveResolution L) (n : ℕ)
    (a : K.obj (AddCommGrpCat.of (ULift.{s} ℤ)) ⟶ I.cochainComplex.X (n : ℤ))
    (ha : a ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1) = 0) :
    (I.isoRightDerivedObjCochain Γ n).hom
        (originalSectionsExtEquivOfResolution constantAdj I n
          (I.extEquivCohomologyClass.symm
            (.mk (Cocycle.fromSingleMk a (zero_add (n : ℤ)) ((n : ℤ) + 1) rfl ha)))) =
      let E := (Γ.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
      originalSectionCycleClass E (n : ℤ)
        ((integerHomSectionsIso constantAdj).hom.app _ a) (by
          have he : (integerHomSectionsIso constantAdj).hom.app _
              (a ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1)) =
            Γ.map (I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1))
              ((integerHomSectionsIso constantAdj).hom.app _ a) :=
            ConcreteCategory.congr_hom
              ((integerHomSectionsIso constantAdj).hom.naturality
                (I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1))) a
          have hz : (integerHomSectionsIso constantAdj).hom.app _
              (a ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1)) = 0 := by
            rw [ha]
            exact map_zero _
          exact he.symm.trans hz) := by
  exact InjectiveResolution.extRightDerivedAddEquiv_cocycle_natTrans
    (K.obj (AddCommGrpCat.of (ULift.{s} ℤ)))
    (integerHomSectionsIso constantAdj).hom I n a ha

/-- Normalization of the original natural-degree representative under the
same Gamma comparison. -/
theorem originalSectionsExtEquivOfResolution_extMk
    {L : C} (I : InjectiveResolution L) (n : ℕ)
    (a : K.obj (AddCommGrpCat.of (ULift.{s} ℤ)) ⟶ I.cocomplex.X n)
    (ha : a ≫ I.cocomplex.d n (n + 1) = 0) :
    (I.isoRightDerivedObjCochain Γ n).hom
        (originalSectionsExtEquivOfResolution constantAdj I n (I.extMk a (n + 1) rfl ha)) =
      let E := (Γ.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
      originalSectionCycleClass E (n : ℤ)
        ((integerHomSectionsIso constantAdj).hom.app _
          (a ≫ (I.cochainComplexXIso n n rfl).inv)) (by
          let a' : K.obj (AddCommGrpCat.of (ULift.{s} ℤ)) ⟶ I.cochainComplex.X (n : ℤ) :=
            a ≫ (I.cochainComplexXIso n n rfl).inv
          have ha' : a' ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1) = 0 := by
            rw [I.cochainComplex_d _ _ n (n + 1) rfl (by simp)]
            simp only [a', Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% ha, zero_comp]
          have he : (integerHomSectionsIso constantAdj).hom.app _
              (a' ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1)) =
            Γ.map (I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1))
              ((integerHomSectionsIso constantAdj).hom.app _ a') :=
            ConcreteCategory.congr_hom
              ((integerHomSectionsIso constantAdj).hom.naturality
                (I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1))) a'
          have hz : (integerHomSectionsIso constantAdj).hom.app _
              (a' ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1)) = 0 := by
            rw [ha']
            exact map_zero _
          exact he.symm.trans hz) := by
  let a' : K.obj (AddCommGrpCat.of (ULift.{s} ℤ)) ⟶ I.cochainComplex.X (n : ℤ) :=
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
  exact originalSectionsExtEquivOfResolution_cocycle constantAdj I n a' ha'

include hc in
omit [G.Additive] in
/-- Original Ext pullback agrees with the independently defined resolution
section map, for every actual augmentation-compatible lift. -/
theorem originalSectionsExtEquivOfResolution_pullback
    {L : C}
    (I : InjectiveResolution L) (J : InjectiveResolution (F.obj L))
    (φ : InjectiveResolution.ExactFunctor.mappedResolution F I ⟶
      J.cocomplex)
    (hφ : F.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0)
    (n : ℕ) (b : Abelian.Ext.{w} (K.obj (AddCommGrpCat.of (ULift.{s} ℤ))) L n) :
    originalSectionsExtEquivOfResolution constantAdj' J n
        (F.extPrecompMap (c.app (AddCommGrpCat.of (ULift.{s} ℤ))).inv L n b) =
      rightDerivedSectionsPullbackOfLift imageAdj Γ e I J φ n
        (originalSectionsExtEquivOfResolution constantAdj I n b) := by
  obtain ⟨a, ha, rfl⟩ := I.extMk_surjective b (n + 1) rfl
  apply ((J.isoRightDerivedObjCochain Δ n).addCommGroupIsoToAddEquiv).injective
  change (J.isoRightDerivedObjCochain Δ n).hom
      (originalSectionsExtEquivOfResolution constantAdj' J n
        (F.extPrecompMap (c.app (AddCommGrpCat.of (ULift.{s} ℤ))).inv L n
          (I.extMk a (n + 1) rfl ha))) =
    (J.isoRightDerivedObjCochain Δ n).hom
      (rightDerivedSectionsPullbackOfLift imageAdj Γ e I J φ n
        (originalSectionsExtEquivOfResolution constantAdj I n (I.extMk a (n + 1) rfl ha)))
  rw [integerSourcePullback_extMk (F := F) c I J φ hφ,
    originalSectionsExtEquivOfResolution_extMk]
  simp only [rightDerivedSectionsPullbackOfLift, ConcreteCategory.comp_apply]
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply,
    originalSectionsExtEquivOfResolution_extMk, originalSectionCycleClass_map]
  congr 1
  change (integerHomSectionsIso constantAdj').hom.app _
      (((c.app (AddCommGrpCat.of (ULift.{s} ℤ))).inv ≫
        F.map a ≫ φ.f n) ≫ (J.cochainComplexXIso n n rfl).inv) =
    (resolutionSectionsPullback imageAdj Γ e I J φ).f (n : ℤ)
      ((integerHomSectionsIso constantAdj).hom.app _
        (a ≫ (I.cochainComplexXIso n n rfl).inv))
  let a' : K'.obj (AddCommGrpCat.of (ULift.{s} ℤ)) ⟶ F.obj
        (I.cochainComplex.X (n : ℤ)) :=
    (c.app (AddCommGrpCat.of (ULift.{s} ℤ))).inv ≫
      F.map (a ≫ (I.cochainComplexXIso n n rfl).inv)
  have hn : (integerHomSectionsIso constantAdj').hom.app _
      (a' ≫ (InjectiveResolution.ExactFunctor.extendedLift F I J φ).f (n : ℤ)) =
    Δ.map
      ((InjectiveResolution.ExactFunctor.extendedLift F I J φ).f (n : ℤ))
        ((integerHomSectionsIso constantAdj').hom.app _ a') :=
    ConcreteCategory.congr_hom
      ((integerHomSectionsIso constantAdj').hom.naturality
        ((InjectiveResolution.ExactFunctor.extendedLift F I J φ).f (n : ℤ))) a'
  have hp := integerHomSectionsIso_pullback constantAdj imageAdj constantAdj' e c hc
    (a ≫ (I.cochainComplexXIso n n rfl).inv)
  have hn' := hn.trans (congrArg
    (fun x => Δ.map
      ((InjectiveResolution.ExactFunctor.extendedLift F I J φ).f (n : ℤ)) x) hp)
  have hψ : (resolutionSectionsPullback imageAdj Γ e I J φ).f (n : ℤ) =
      (unitSectionsNatTrans imageAdj Γ e).app (I.cochainComplex.X (n : ℤ)) ≫
        Δ.map
          ((InjectiveResolution.ExactFunctor.extendedLift F I J φ).f (n : ℤ)) := rfl
  rw [hψ, ConcreteCategory.comp_apply]
  refine Eq.trans ?_ hn'
  dsimp only [a']
  congr 1
  rw [InjectiveResolution.ExactFunctor.extendedLift_f, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

section CanonicalDerived

variable [HasDerivedCategory.{dC} C]
  [HasDerivedCategory.{dD} D]
  [HasDerivedCategory.{dV} AddCommGrpCat.{s}]

include hc in
/-- Original Ext-based pullback agrees with homology of the actual canonical
D+ global-sections map, retaining all native resolution and single comparisons. -/
theorem originalSectionsExtEquiv_pullback
    (L : C) (n : ℕ) (a : Abelian.Ext.{w} (K.obj (AddCommGrpCat.of (ULift.{s} ℤ))) L n) :
    originalSectionsExtEquiv constantAdj' (F.obj L) n
        (F.extPrecompMap (c.app (AddCommGrpCat.of (ULift.{s} ℤ))).inv L n a) =
      rightDerivedUnitSectionsPullback imageAdj Γ e L n
        (originalSectionsExtEquiv constantAdj L n a) := by
  let I := injectiveResolution L
  let J := injectiveResolution (F.obj L)
  let φ := InjectiveResolution.ExactFunctor.lift F I J (𝟙 _)
  have hφ : F.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0 := by
    simpa only [Category.id_comp] using
      InjectiveResolution.ExactFunctor.lift_commutes_zero F I J (𝟙 _)
  rw [rightDerivedUnitSectionsPullback_eq_resolution imageAdj Γ e I J φ hφ]
  have hψ :
      (unitSectionsPullbackComplex imageAdj Γ e I.cochainComplexPlus ≫
        Δ.mapCochainComplexPlus.map
          (resolutionLiftPlus (F := F) I J φ)).hom =
        resolutionSectionsPullback imageAdj Γ e I J φ := by
    ext i
    rfl
  rw [hψ]
  exact originalSectionsExtEquivOfResolution_pullback constantAdj imageAdj constantAdj'
    e c hc I J φ hφ n a

end CanonicalDerived

end CategoryTheory.Adjunction
