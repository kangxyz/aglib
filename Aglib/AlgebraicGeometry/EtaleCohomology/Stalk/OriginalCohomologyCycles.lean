/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.OriginalCohomology
public import
  Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedPostcompResolution
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.CocycleComparison

/-! # Original represented cohomology on actual resolution cycles

The existing original Ext comparison with the resolution presheaf sends each
actual represented cocycle to its original section cycle class. The original
coefficient and independent Ext universes are retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open CochainComplex.HomComplex

universe u w

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Etale)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The original Ext-to-presheaf comparison retains the represented section
cycle and the native exact evaluation/homology comparison in every degree. -/
theorem originalCohomologyResolutionEquivOfResolution_cocycle
    {F : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution F) (q : ℕ)
    (a : Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1} (Scheme.smallEtaleTopology X)
      ((siteBaseChange f).obj U) ⟶ I.cochainComplex.X (q : ℤ))
    (ha : a ≫ I.cochainComplex.d (q : ℤ) ((q : ℤ) + 1) = 0) :
    let P := directImagePresheaf f
    let E := (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op U)
    let K := (P.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    E.map (I.isoRightDerivedObjCochain P q).hom
        (originalCohomologyResolutionEquivOfResolution f U I q
          (I.extEquivCohomologyClass.symm
            (.mk (Cocycle.fromSingleMk a (zero_add (q : ℤ)) ((q : ℤ) + 1) rfl ha)))) =
      ((K.sc (q : ℤ)).mapHomologyIso E).hom
        (addCommGrpCycleClass ((E.mapHomologicalComplex (.up ℤ)).obj K) (q : ℤ)
          ((directImagePresheafRepresentedIso f U).hom.app _ a) (by
            have he := ConcreteCategory.congr_hom
              ((directImagePresheafRepresentedIso f U).hom.naturality
                (I.cochainComplex.d (q : ℤ) ((q : ℤ) + 1))) a
            change (directImagePresheafRepresentedIso f U).hom.app _
                (a ≫ I.cochainComplex.d (q : ℤ) ((q : ℤ) + 1)) = _ at he
            rw [ha, map_zero] at he
            exact he.symm)) := by
  dsimp only
  let P := directImagePresheaf f
  let E := (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op U)
  let α := (directImagePresheafRepresentedIso f U).hom
  let x := I.extEquivCohomologyClass.symm
    (.mk (Cocycle.fromSingleMk a (zero_add (q : ℤ)) ((q : ℤ) + 1) rfl ha))
  have hp := Sheaf.ModuleCoefficients.rightDerivedPostcompIso_hom_resolution_cochain
    P E I q
  have hr := InjectiveResolution.extRightDerivedAddEquiv_cocycle_natTrans
    (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1} (Scheme.smallEtaleTopology X)
      ((siteBaseChange f).obj U)) α I q a ha
  change E.map (I.isoRightDerivedObjCochain P q).hom
    ((Sheaf.ModuleCoefficients.rightDerivedPostcompIso P E q).hom.app F
      ((NatTrans.rightDerived α q).app F
        (I.extRightDerivedAddEquiv _ q x))) = _
  have he := ConcreteCategory.congr_hom hp
    ((NatTrans.rightDerived α q).app F (I.extRightDerivedAddEquiv _ q x))
  let e := ((((P.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).sc
    (q : ℤ)).mapHomologyIso E)
  exact he.trans (congrArg e.hom hr)

end AlgebraicGeometry.Scheme.EtaleCohomology
