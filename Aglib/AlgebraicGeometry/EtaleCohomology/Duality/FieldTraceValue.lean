/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.MixedEdgeTrace
public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.FieldDirectImageValue
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ProperTopTraceBound
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.DerivedPullback
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.TraceTransport

/-! Original field trace value on every roots Ext class. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
open Scheme.OverField Scheme.OverField.Curve
universe u wB wY
attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : FScheme k} (hY : Curve.Properties Y)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  [HasDerivedCategory.{wB} (ModuleSheaf (Base k) (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wY} (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n)))]

local instance : HasExt.{u + 2} (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n))) :=
  SheafOfModules.hasExt (constantRing Y.left (ULift.{u + 1} (ZMod n)))
local instance : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Y.left) := hasExtStandard Y.left

/-- Every original roots class evaluates to its actual constant-unit trace section. -/
theorem properCurveFieldOrdinaryTrace_value
    (x : Ext.{u + 2} (moduleUnit Y.left (ULift.{u + 1} (ZMod n)))
      (moduleRootsOfUnity Y.left n) 2) :
    let Λ := ULift.{u + 1} (ZMod n)
    let D := ModuleSheaf (Base k) Λ
    let U := moduleUnit (Base k) Λ
    let F := DerivedCategory.Plus.singleFunctor D 0
    let M := (DerivedCategory.Plus.singleFunctor (ModuleSheaf Y.left Λ) 0).obj
      (moduleRootsOfUnity Y.left n)
    let K := (moduleDerivedDirectImage Λ Y.hom).obj M
    letI := DerivedCategory.Plus.isLE_of_original_homology K 2
      (properCurveRootsDirectImage_isZero_homology hY n hn hunit)
    let e := constantModuleDerivedUnitPullbackIso Y.hom n
    let z := (moduleDerivedAdjunction Λ Y.hom).shiftedHomEquiv 2 (F.obj U) M (e.hom ≫ x.homPlus)
    let Γ := moduleGlobalSections (Base k) Λ
    let scalar := Curves.traceAddEquiv hY n hn hunit (modulePoint_globalLevelInvertible n hunit)
      (moduleRootsUnitExtCohomologyAddEquiv Y.left n 2 x)
    let s := Γ.map (moduleUnitConstantIso (Base k) Λ).hom
      ((moduleGlobalSectionsAdjunction (Base k) Λ).unit.app (ModuleCat.of Λ Λ) (ULift.up scalar))
    z ≫ DerivedCategory.Plus.ordinaryTraceFromTop 2 K U
      (properCurveTopDirectImageTraceIso hY n hn hunit).hom =
      F.map ((moduleFieldUnitSectionsEquiv k Λ U).symm s) := by
  dsimp only
  let Λ := ULift.{u + 1} (ZMod n)
  let M := (DerivedCategory.Plus.singleFunctor (ModuleSheaf Y.left Λ) 0).obj
    (moduleRootsOfUnity Y.left n)
  let K := (moduleDerivedDirectImage Λ Y.hom).obj M
  let := DerivedCategory.Plus.isLE_of_original_homology K 2
    (properCurveRootsDirectImage_isZero_homology hY n hn hunit)
  rw [constantModuleDerivedUnitPullbackIso_eq]
  refine (DerivedCategory.Plus.ordinaryTraceFromTop_homology_value 2 _ _).trans ?_
  apply congrArg (DerivedCategory.Plus.singleFunctor (ModuleSheaf (Base k) Λ) 0).map
  apply (moduleFieldUnitSectionsEquiv k Λ (moduleUnit (Base k) Λ)).injective
  exact ((moduleFieldDirectImageHomology_map_value k Y.hom n (moduleRootsOfUnity Y.left n) 2 x
    (properCurveTopDirectImageTraceIso hY n hn hunit).hom).symm.trans
      (properCurveTopDirectImageTraceIso_hom_value hY n hn hunit x)).trans
        ((moduleFieldUnitSectionsEquiv k Λ (moduleUnit (Base k) Λ)).apply_symm_apply _).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
