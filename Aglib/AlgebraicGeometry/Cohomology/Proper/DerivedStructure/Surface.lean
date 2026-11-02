/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.DerivedStructure.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Proper.BirationalStructureSheaf
public import Aglib.AlgebraicGeometry.Cohomology.Proper.FibreDimension.HigherDirectImage
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.AcyclicSingle
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.QuasiCoherent

/-! # The original derived structure unit above a normal surface

Actual first higher-image vanishing and the proved higher-degree fibre bound
make the original structural unit invertible. No desired-unit premise is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

local instance surfaceStructureDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The same original derived structure unit is invertible once actual R1
vanishes on a proper birational integral surface map with normal target. -/
theorem isIso_moduleDerivedPushforwardUnit_of_surface_R1_isZero
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
    (f : Y ⟶ X) [IsProper f] [IsDominant f] (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hdY : topologicalKrullDim Y ≤ 2)
    (hR1 : IsZero (((pushforward f).rightDerived 1).obj
      (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf))) :
    IsIso (moduleDerivedPushforwardUnit X f) := by
  let O : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let F := pushforward f
  let : O.IsQuasicoherent := isQuasicoherent_unit Y
  have hacyclic (n : ℕ) : IsZero ((F.rightDerived (n + 1)).obj O) := by
    by_cases hn : n = 0
    · subst n
      exact hR1
    · exact isZero_higherDirectImage_of_proper_birational_surface f hff hdY O
        (affineLocallyFiniteType_unit Y) (n + 1) (by omega)
  let : IsIso (F.rightDerivedFunctorPlusUnit.app
      ((CochainComplex.singleFunctorPlus Y.Modules 0).obj O)) :=
    F.isIso_rightDerivedFunctorPlusUnit_single_of_isZero_rightDerived_succ O hacyclic
  let E : F.mapCochainComplexPlus.obj
      ((CochainComplex.singleFunctorPlus Y.Modules 0).obj O) ≅
        (CochainComplex.singleFunctorPlus X.Modules 0).obj (F.obj O) :=
    (CochainComplex.plus X.Modules).isoMk
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app O)
  have hsingle : IsIso (F.rightDerivedSingleUnit O) := by
    change IsIso (DerivedCategory.Plus.Q.map E.inv ≫
      F.rightDerivedFunctorPlusUnit.app
        ((CochainComplex.singleFunctorPlus Y.Modules 0).obj O))
    infer_instance
  let := hsingle
  let φ := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let : IsIso φ := isIso_unitToPushforwardObjUnit_of_isProper_birational f hX hff
  change IsIso ((DerivedCategory.Plus.singleFunctor X.Modules 0).map φ ≫
    F.rightDerivedSingleUnit O)
  infer_instance

end AlgebraicGeometry.Scheme.Cohomology
