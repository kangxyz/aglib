/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.RelativeTrace
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.FieldTraceValue
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.DiagonalFibreTrace
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.DerivedUnitEndRestriction

/-! The original relative trace normalized on the original positive diagonal. -/

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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Trace one of the actual class normalizes the original ordinary field trace. -/
theorem properCurveFieldOrdinaryTrace_normalized
    (x : Ext.{u + 2} (moduleUnit Y.left (ULift.{u + 1} (ZMod n)))
      (moduleRootsOfUnity Y.left n) 2)
    (hx : Curves.traceAddEquiv hY n hn hunit (modulePoint_globalLevelInvertible n hunit)
      (moduleRootsUnitExtCohomologyAddEquiv Y.left n 2 x) = 1) :
    let Λ := ULift.{u + 1} (ZMod n)
    let D := ModuleSheaf (Base k) Λ
    let U := moduleUnit (Base k) Λ
    let I := (DerivedCategory.Plus.singleFunctor D 0).obj U
    let M := (DerivedCategory.Plus.singleFunctor (ModuleSheaf Y.left Λ) 0).obj
      (moduleRootsOfUnity Y.left n)
    let K := (moduleDerivedDirectImage Λ Y.hom).obj M
    letI := DerivedCategory.Plus.isLE_of_original_homology K 2
      (properCurveRootsDirectImage_isZero_homology hY n hn hunit)
    let e := constantModuleDerivedUnitPullbackIso Y.hom n
    let z := (moduleDerivedAdjunction Λ Y.hom).shiftedHomEquiv 2 I M (e.hom ≫ x.homPlus)
    z ≫ DerivedCategory.Plus.ordinaryTraceFromTop 2 K U
      (properCurveTopDirectImageTraceIso hY n hn hunit).hom = 𝟙 I := by
  have h := properCurveFieldOrdinaryTrace_value hY n hn hunit x
  dsimp only at h ⊢
  rw [hx] at h
  let Λ := ULift.{u + 1} (ZMod n)
  let U := moduleUnit (Base k) Λ
  let F := DerivedCategory.Plus.singleFunctor (ModuleSheaf (Base k) Λ) 0
  let E := moduleFieldUnitSectionsEquiv k Λ U
  let s := (moduleGlobalSections (Base k) Λ).map (moduleUnitConstantIso (Base k) Λ).hom
    ((moduleGlobalSectionsAdjunction (Base k) Λ).unit.app (ModuleCat.of Λ Λ)
      (ULift.up (1 : ZMod n)))
  have hs : s = E (𝟙 U) := (moduleFieldUnitSectionsEquiv_id k Λ).symm
  change _ = F.map (E.symm s) at h
  exact h.trans ((congrArg (fun t => F.map (E.symm t)) hs).trans
    ((congrArg F.map (E.symm_apply_apply (𝟙 U))).trans (F.map_id U)))

open Scheme.OverField.Curve.PointDivisor

universe wZ wEZ

variable [HasDerivedCategory.{wZ} (ModuleSheaf (pullback Y.hom Y.hom) (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wEZ} (ModuleSheaf (pullback Y.hom Y.hom) (ULift.{u + 1} (ZMod n)))]
  (o : Base k ⟶ Y.left) (ho : o ≫ Y.hom = 𝟙 (Base k))

local instance : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} (pullback Y.hom Y.hom)) :=
  hasExtStandard (pullback Y.hom Y.hom)

/-- The original relative trace is normalized on the original positive diagonal class. -/
abbrev properCurveDiagonalOrdinaryTraceExistsUniqueNormalized :=
  let Λ := ULift.{u + 1} (ZMod n)
  let p := Y.hom
  let q := pullback.fst p p
  let i := diagonalSectionFibreMap p o ho
  let hi₁ : i ≫ q = 𝟙 Y.left := pullback.lift_fst _ _ _
  let hi₂ : i ≫ pullback.snd p p = p ≫ o := pullback.lift_snd _ _ _
  let hiZ := GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible q n
    (modulePoint_globalLevelInvertible n hunit)
  letI : SmoothOfRelativeDimension 1 p := hY.smooth
  letI : IsProper p := hY.proper
  letI : IsNoetherian Y.left := curveProperties_isNoetherian hY
  letI : ConnectedSpace Y.left := curveProperties_connectedSpace hY
  letI : NeZero n := ⟨ne_of_gt hn⟩
  let x := Kummer.diagonalModuleKummerClass p n hn hiZ
  let y := moduleRootsUnitExtPullback i n hn hiZ 2 x
  let hex := properCurveProductTraceExistsUniqueClassRestriction hY n hn hunit o ho i hi₁ hi₂
  let hx := Curves.traceAddEquiv_diagonalModuleKummerClass_pullback_sectionFibre
    hY o ho n hn hunit hiZ
  let hy := properCurveFieldOrdinaryTrace_normalized hY n hn hunit y hx
  let hG := moduleDerivedInverseImage_map_injective_singleUnit_end o Λ _root_.isAddTorsion_of_finite
  existsUnique_originalTrace_normalized hex x hy hG

/-- The same original trace, in the degree minus two used by the diagonal cup identity. -/
abbrev properCurveDiagonalTraceExistsNormalized :=
  ShiftedHom.exists_originalShiftedTrace_normalized
    (properCurveDiagonalOrdinaryTraceExistsUniqueNormalized hY n hn hunit o ho)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
