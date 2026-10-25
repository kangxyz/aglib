/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.CyclePairing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartTargetCycles

/-! # Shared witness heads for original chart cycle producers

Both source and target producers retain the same regular term-and-projection
predicate before the actual fibre-product geometry is substituted. All native
classes, resolution maps and chart sources are unchanged.
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

/-- The original represented cocycle supplies its actual source cycle,
retaining the shared term-and-projection witness head. -/
theorem originalHigherSection_cycleWitness_extMk {X S : Scheme.{u}}
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] (f : X ⟶ S) (U : S.Etale)
    {F : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution F) (q : ℕ)
    (a : Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
      (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U) ⟶ I.cocomplex.X q)
    (ha : a ≫ I.cocomplex.d q (q + 1) = 0) :
    let K := ((directImage f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    Functor.CycleWitness
      (fun z => (K.iCycles (q : ℤ)).hom.app (op U) z)
      (fun z => (K.homologyπ (q : ℤ)).hom.app (op U) z)
      (Sheaf.Hypercohomology.sectionsEquiv.{u + 1}
        (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U) _
        (a ≫ (I.cochainComplexXIso q q rfl).inv))
      ((I.isoRightDerivedObjCochain (directImage f) q).hom.hom.app (op U)
        (((resolutionCohomologyToHigherDirectImage f q).app F).app (op U)
          (originalCohomologyResolutionEquiv f U F q
            (I.extMk a (q + 1) rfl ha)))) := by
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
  rw [hrep, originalCohomologyResolutionEquiv_eq_ofResolution f U I]
  exact originalHigherSection_exists_resolution_cycle f U I q a' ha'


variable {X S' : Scheme.{u}} (V : X.Etale) (t : V.left ⟶ S')
  [hBaseExt : HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over V) AddCommGrpCat.{u + 1})]
  [hChartExt : HasExt.{e} (AbelianSheaf.{u, u + 1} V.left)]

local instance : HasExt.{w}
    (AbelianSheaf.{u, u + 1} ((Functor.fromPUnit X).obj V.right)) := hBaseExt

local instance : HasExt.{e}
    (Sheaf ((𝟭 Scheme.{u}).obj V.left).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  hChartExt

/-- The accepted native chart calculation at the same regular cycle-witness
head used by representative elimination and source-target pairing. -/
theorem originalChartSection_cycleWitness_extMk
    {F : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution F)
    (J : InjectiveResolution ((inverseImage V.hom).obj F)) (q : ℕ)
    (a : Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
      (Scheme.smallEtaleTopology X) V ⟶ I.cocomplex.X q)
    (ha : a ≫ I.cocomplex.d q (q + 1) = 0) :
    let T := ((directImage t).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
    let φ := InjectiveResolution.ExactFunctor.lift (inverseImage V.hom) I J (𝟙 _)
    let Φ := InjectiveResolution.ExactFunctor.extendedLift (inverseImage V.hom) I J φ
    Functor.CycleWitness
      (fun z => (directImageGlobalSectionsIso t).hom.app _
        ((globalSections S').map (T.iCycles (q : ℤ)) z))
      (fun z => (globalSections S').map (T.homologyπ (q : ℤ)) z)
      ((globalSections V.left).map (Φ.f (q : ℤ))
        ((Continuity.pullbackSectionsEtaleEvaluationIso
          (I.cochainComplex.X (q : ℤ)) V).inv
            (Sheaf.Hypercohomology.sectionsEquiv.{u + 1}
              (Scheme.smallEtaleTopology X) V _
              (a ≫ (I.cochainComplexXIso q q rfl).inv))))
      ((globalSections S').map (J.isoRightDerivedObjCochain (directImage t) q).hom
        (cohomologyToHigherSections t ((inverseImage V.hom).obj F) q
          (originalCohomologyChartEquiv V F q (I.extMk a (q + 1) rfl ha)))) :=
  Functor.cycleWitness_of_reversed _ _ _ _
    (originalChartSection_cycles_extMk V t I J q a ha)

end AlgebraicGeometry.Scheme.EtaleCohomology
