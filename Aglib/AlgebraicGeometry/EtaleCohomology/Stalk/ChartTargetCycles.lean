/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackCycleSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartResolutionSections

/-! # Actual chart cocycles as higher-image cycle sections

The original chart class of a represented cocycle has an actual higher-image
cycle section for every morphism out of the chart. The entire construction uses
the chart's native scheme and arrow, before any fibre-product specialization.
Base, slice and chart Ext universes remain independent.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex Opposite
open CochainComplex.HomComplex

universe u w s e

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

private theorem cohomologyToHigherSections_cycles_of_extMk {X S : Scheme.{u}}
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] (f : X ⟶ S)
    {F : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution F) (q : ℕ)
    (a : (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ I.cocomplex.X q)
    (ha : a ≫ I.cocomplex.d q (q + 1) = 0)
    (x : Sheaf.H.{w} F q) (hx : x = I.extMk a (q + 1) rfl ha) :
    let K := ((directImage f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    ∃ z : (globalSections S).obj (K.cycles (q : ℤ)),
      (globalSections S).map (K.iCycles (q : ℤ)) z =
          (directImageGlobalSectionsIso f).inv.app _
            ((constantIntegerHomGlobalSectionsIso X).hom.app _
              (a ≫ (I.cochainComplexXIso q q rfl).inv)) ∧
        (globalSections S).map (I.isoRightDerivedObjCochain (directImage f) q).hom
          (cohomologyToHigherSections f F q x) =
            (globalSections S).map (K.homologyπ (q : ℤ)) z := by
  subst x
  exact cohomologyToHigherSections_cycles_extMk f I q a ha


variable {X S' : Scheme.{u}} (V : X.Etale) (t : V.left ⟶ S')
  [hBaseExt : HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over V) AddCommGrpCat.{u + 1})]
  [hChartExt : HasExt.{e} (AbelianSheaf.{u, u + 1} V.left)]

local instance chartTargetCyclesHasBaseExt : HasExt.{w}
    (AbelianSheaf.{u, u + 1} ((Functor.fromPUnit X).obj V.right)) := hBaseExt

local instance chartTargetCyclesHasChartExt : HasExt.{e}
    (Sheaf ((𝟭 Scheme.{u}).obj V.left).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  hChartExt

/-- The original chart class of an actual represented cocycle has a higher-image
cycle whose term is the original chart section followed by the native lift. -/
theorem originalChartSection_cycles_extMk
    {F : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution F)
    (J : InjectiveResolution ((inverseImage V.hom).obj F)) (q : ℕ)
    (a : Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
      (Scheme.smallEtaleTopology X) V ⟶ I.cocomplex.X q)
    (ha : a ≫ I.cocomplex.d q (q + 1) = 0) :
    let T := ((directImage t).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
    let φ := InjectiveResolution.ExactFunctor.lift (inverseImage V.hom) I J (𝟙 _)
    let Φ := InjectiveResolution.ExactFunctor.extendedLift (inverseImage V.hom) I J φ
    ∃ z : (globalSections S').obj (T.cycles (q : ℤ)),
      (globalSections S').map (J.isoRightDerivedObjCochain (directImage t) q).hom
          (cohomologyToHigherSections t ((inverseImage V.hom).obj F) q
            (originalCohomologyChartEquiv V F q (I.extMk a (q + 1) rfl ha))) =
        (globalSections S').map (T.homologyπ (q : ℤ)) z ∧
      (directImageGlobalSectionsIso t).hom.app _
          ((globalSections S').map (T.iCycles (q : ℤ)) z) =
        (globalSections V.left).map (Φ.f (q : ℤ))
          ((Continuity.pullbackSectionsEtaleEvaluationIso
            (I.cochainComplex.X (q : ℤ)) V).inv
              (Sheaf.Hypercohomology.sectionsEquiv.{u + 1}
                (Scheme.smallEtaleTopology X) V _
                (a ≫ (I.cochainComplexXIso q q rfl).inv))) := by
  let φ := InjectiveResolution.ExactFunctor.lift (inverseImage V.hom) I J (𝟙 _)
  have hφ : (inverseImage V.hom).map (I.ι.f 0) ≫ φ.f 0 = 𝟙 _ ≫ J.ι.f 0 :=
    InjectiveResolution.ExactFunctor.lift_commutes_zero (inverseImage V.hom) I J (𝟙 _)
  let b := chartComparisonSource V ≫ (inverseImage V.hom).map a ≫ φ.f q
  have hb : b ≫ J.cocomplex.d q (q + 1) = 0 := by
    simpa only [b, Category.assoc, comp_zero] using congrArg
      (fun k => chartComparisonSource V ≫ k)
      (InjectiveResolution.ExactFunctor.mappedCycle_comp_d φ q a ha)
  have hx : originalCohomologyChartEquiv V F q (I.extMk a (q + 1) rfl ha) =
      J.extMk b (q + 1) rfl hb := by
    rw [originalCohomologyChartEquiv_apply.{u, w, s, e}]
    have h := InjectiveResolution.ExactFunctor.mk₀_comp_extMk_mapExactFunctor_comp_mk₀
      (inverseImage V.hom) I J (𝟙 _) φ hφ a ha (chartComparisonSource V)
    simpa only [Ext.comp_mk₀_id] using h
  obtain ⟨z, hz, hp⟩ := cohomologyToHigherSections_cycles_of_extMk
    (X := V.left) (S := S') t J q b hb
      (originalCohomologyChartEquiv V F q (I.extMk a (q + 1) rfl ha)) hx
  refine ⟨z, hp, ?_⟩
  have hc := ConcreteCategory.congr_hom
    ((directImageGlobalSectionsIso t).app (J.cochainComplex.X (q : ℤ))).inv_hom_id
      ((constantIntegerHomGlobalSectionsIso V.left).hom.app _
        (b ≫ (J.cochainComplexXIso q q rfl).inv))
  exact (congrArg ((directImageGlobalSectionsIso t).hom.app
    (J.cochainComplex.X (q : ℤ))) hz).trans
      (hc.trans (chartComparisonSource_sections_extendedLift V I J φ q a))

end AlgebraicGeometry.Scheme.EtaleCohomology
