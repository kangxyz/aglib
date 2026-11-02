/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GlobalSectionsCycles
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackComposition
public import Aglib.CategoryTheory.Abelian.Injective.ExactFunctorSections

/-! # Original cohomology pullback on actual higher-image cycle sections

Original Ext pullback supplies source and target cycle sections in any actual
resolutions. Their terms are related by the original global-section complex
map. The two Ext universes are independent; no derived-category model or
base-change isomorphism is required.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open CochainComplex.HomComplex

universe u w w'

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

/-- The original Ext class of a native resolution cocycle has an actual
higher-image cycle section with its original terminal-transported term. -/
theorem cohomologyToHigherSections_cycles_extMk {X S : Scheme.{u}}
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] (f : X ⟶ S)
    {F : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution F) (q : ℕ)
    (a : (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ I.cocomplex.X q)
    (ha : a ≫ I.cocomplex.d q (q + 1) = 0) :
    let K := ((directImage f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    ∃ z : (globalSections S).obj (K.cycles (q : ℤ)),
      (globalSections S).map (K.iCycles (q : ℤ)) z =
          (directImageGlobalSectionsIso f).inv.app _
            ((constantIntegerHomGlobalSectionsIso X).hom.app _
              (a ≫ (I.cochainComplexXIso q q rfl).inv)) ∧
        (globalSections S).map (I.isoRightDerivedObjCochain (directImage f) q).hom
          (cohomologyToHigherSections f F q (I.extMk a (q + 1) rfl ha)) =
            (globalSections S).map (K.homologyπ (q : ℤ)) z := by
  let a' := a ≫ (I.cochainComplexXIso q q rfl).inv
  have ha' : a' ≫ I.cochainComplex.d (q : ℤ) ((q : ℤ) + 1) = 0 := by
    rw [I.cochainComplex_d _ _ q (q + 1) rfl (by simp)]
    simp only [a', Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% ha, zero_comp]
  have hrep : I.extMk a (q + 1) rfl ha =
      I.extEquivCohomologyClass.symm
        (.mk (Cocycle.fromSingleMk a' (zero_add (q : ℤ)) ((q : ℤ) + 1) rfl ha')) := by
    apply I.extEquivCohomologyClass.injective
    rw [Equiv.apply_symm_apply, InjectiveResolution.extEquivCohomologyClass_extMk]
    simp only [a', Nat.cast_add, Nat.cast_one]
  rw [hrep]
  exact cohomologyToHigherSections_exists_resolution_cycle f I q a' ha'

private theorem original_section_extendedLift {X X' : Scheme.{u}} (g : X' ⟶ X)
    {F : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution F)
    (J : InjectiveResolution ((inverseImage g).obj F))
    (φ : InjectiveResolution.ExactFunctor.mappedResolution (inverseImage g) I ⟶ J.cocomplex)
    (q : ℕ)
    (a : (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ I.cocomplex.X q) :
    (constantIntegerHomGlobalSectionsIso X').hom.app _
        ((((inverseImageConstantIso g).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv ≫
          (inverseImage g).map a ≫ φ.f q) ≫ (J.cochainComplexXIso q q rfl).inv) =
      (globalSections X').map
        ((InjectiveResolution.ExactFunctor.extendedLift (inverseImage g) I J φ).f (q : ℤ))
          (globalSectionsPullback g (I.cochainComplex.X (q : ℤ))
            ((constantIntegerHomGlobalSectionsIso X).hom.app _
              (a ≫ (I.cochainComplexXIso q q rfl).inv))) := by
  exact InjectiveResolution.ExactFunctor.extendedLift_sections
    (inverseImage g) I J φ
    (((inverseImageConstantIso g).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv)
    (globalSections X') (constantIntegerHomGlobalSectionsIso X') q a _
    (constantIntegerHomGlobalSectionsIso_pullback g
      (a ≫ (I.cochainComplexXIso q q rfl).inv))

/-- Source and target original global cohomology classes admit actual higher-image
cycle sections with exactly the original pullback relation on their terms. -/
theorem cohomologyToHigherSections_pullback_cycles {X S X' S' : Scheme.{u}}
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} X')]
    (f : X ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    {F : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution F)
    (J : InjectiveResolution ((inverseImage g').obj F)) (q : ℕ) (x : Sheaf.H.{w} F q) :
    let K := ((directImage f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let T := ((directImage f').mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
    let φ := InjectiveResolution.ExactFunctor.lift (inverseImage g') I J (𝟙 _)
    let Φ := InjectiveResolution.ExactFunctor.extendedLift (inverseImage g') I J φ
    ∃ (z : (globalSections S).obj (K.cycles (q : ℤ)))
      (z' : (globalSections S').obj (T.cycles (q : ℤ))),
      (globalSections S).map (I.isoRightDerivedObjCochain (directImage f) q).hom
          (cohomologyToHigherSections f F q x) =
        (globalSections S).map (K.homologyπ (q : ℤ)) z ∧
      (globalSections S').map (J.isoRightDerivedObjCochain (directImage f') q).hom
          (cohomologyToHigherSections f' ((inverseImage g').obj F) q
            (cohomologyPullback.{u, w, w'} g' F q x)) =
        (globalSections S').map (T.homologyπ (q : ℤ)) z' ∧
      (directImageGlobalSectionsIso f').hom.app _
          ((globalSections S').map (T.iCycles (q : ℤ)) z') =
        (globalSections X').map (Φ.f (q : ℤ))
          (globalSectionsPullback g' (I.cochainComplex.X (q : ℤ))
            ((directImageGlobalSectionsIso f).hom.app _
              ((globalSections S).map (K.iCycles (q : ℤ)) z))) := by
  obtain ⟨a, ha, rfl⟩ := I.extMk_surjective x (q + 1) rfl
  let φ := InjectiveResolution.ExactFunctor.lift (inverseImage g') I J (𝟙 _)
  have hφ : (inverseImage g').map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0 := by
    simpa only [Category.id_comp] using
      InjectiveResolution.ExactFunctor.lift_commutes_zero (inverseImage g') I J (𝟙 _)
  let b := ((inverseImageConstantIso g').app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv ≫
    (inverseImage g').map a ≫ φ.f q
  have hb : b ≫ J.cocomplex.d q (q + 1) = 0 := by
    simpa only [b, Category.assoc, comp_zero] using congrArg
      (fun k => ((inverseImageConstantIso g').app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv ≫ k)
      (InjectiveResolution.ExactFunctor.mappedCycle_comp_d φ q a ha)
  obtain ⟨z, hz, hp⟩ := cohomologyToHigherSections_cycles_extMk f I q a ha
  obtain ⟨z', hz', hp'⟩ := cohomologyToHigherSections_cycles_extMk f' J q b hb
  refine ⟨z, z', hp, ?_, ?_⟩
  · rw [cohomologyPullback_extMk_ofLift g' I J φ hφ]
    exact hp'
  · rw [hz, hz']
    have hc (Y Z : Scheme.{u}) (k : Y ⟶ Z) (A : AbelianSheaf.{u, u + 1} Y)
        (s : (globalSections Y).obj A) :
        (directImageGlobalSectionsIso k).hom.app A
          ((directImageGlobalSectionsIso k).inv.app A s) = s :=
      ConcreteCategory.congr_hom ((directImageGlobalSectionsIso k).app A).inv_hom_id s
    rw [hc, hc]
    exact original_section_extendedLift g' I J φ q a

end AlgebraicGeometry.Scheme.EtaleCohomology
