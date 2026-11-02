/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiValueLiftCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiEtalePullbackConstant
public import Aglib.Algebra.Homology.DerivedCategory.Ext.ExactFunctorSquare

/-! # Geometric naturality of the original native-module cohomology comparison

Both geometric maps are the original maps. The proof assembles the actual
coefficient and constant-source squares through the native exact-functor Ext
law, then the genuine value-lift square. No flatness is needed for naturality.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace
open CategoryTheory.Sheaf.BasisAcyclicity
open AlgebraicGeometry.Scheme.Modules

universe u e e'

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] HasExt.standard hasSheafifyLarge
  moduleComparisonEnoughSmall moduleComparisonEnoughRaised
  moduleComparisonAbWRaised moduleComparisonTypeWRaised

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
  [HasExt.{e'} (AbelianSheaf.{u, u + 1} X)]

/-- The original absolute comparison is geometrically natural for every scheme
morphism and quasicoherent native module. The original Zariski cohomology map
has its native Ext range, while the two étale Ext ranges are independent. -/
theorem moduleCohomologyComparison_pullback (M : Y.Modules) [M.IsQuasicoherent]
    (n : ℕ) :
    let p : Sheaf.H.{e} (additiveCoefficient Y M) n →+
        Sheaf.H.{e'} (additiveCoefficient X ((Scheme.Modules.pullback f).obj M)) n :=
      additiveCoefficientCohomologyPullback.{u, e, e'} f M n
    let eY : Sheaf.H.{u + 1} (Scheme.Cohomology.moduleAddSheaf Y M) n ≃+
        Sheaf.H.{e} (additiveCoefficient Y M) n :=
      moduleCohomologyComparison.{u, u + 1, e} Y M n
    let eX : Sheaf.H.{u + 1}
        (Scheme.Cohomology.moduleAddSheaf X ((Scheme.Modules.pullback f).obj M)) n ≃+
        Sheaf.H.{e'} (additiveCoefficient X ((Scheme.Modules.pullback f).obj M)) n :=
      moduleCohomologyComparison.{u, u + 1, e'} X ((Scheme.Modules.pullback f).obj M) n
    eX.toAddMonoidHom.comp (Scheme.Cohomology.moduleCohomologyPullback f M n) =
      p.comp eY.toAddMonoidHom := by
  dsimp only
  apply AddMonoidHom.ext
  intro x
  simp only [AddMonoidHom.comp_apply]
  change moduleCohomologyComparison.{u, u + 1, e'} X
      ((Scheme.Modules.pullback f).obj M) n
      (Scheme.Cohomology.moduleCohomologyPullback f M n x) =
    additiveCoefficientCohomologyPullback.{u, e, e'} f M n
      (moduleCohomologyComparison.{u, u + 1, e} Y M n x)
  let := TopCat.Sheaf.opensAbelianPullback_preservesFiniteLimits.{u, u + 1} f.base
  let := TopCat.Sheaf.opensAbelianPullback_additive.{u, u + 1} f.base
  let := ((Opens.map f.base).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).isLeftAdjoint
  let qY := zariskiInverseImageIntegerIso Y
  let qX := zariskiInverseImageIntegerIso X
  let qO := opensInverseImageIntegerIso f
  let qE := (inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let aY := moduleCoefficientComparison Y M
  let aX := moduleCoefficientComparison X ((Scheme.Modules.pullback f).obj M)
  let b := additiveCoefficientPullback f M
  let c := raisedModulePullback f M
  let y := valueLiftCohomologyMap.{u + 1, u + 2, u, u, u, u + 1} isTerminalTop
    (Scheme.Cohomology.moduleAddSheaf Y M) n x
  have h := Functor.extPrecompMap_postcomp_eq_of_natTrans
    (zariskiInverseImagePullbackIso f).hom
    (qE.inv ≫ (inverseImage f).map qY.inv)
    (qX.inv ≫ (zariskiInverseImage X).map qO.inv)
    ((inverseImage f).map aY ≫ b) ((zariskiInverseImage X).map c ≫ aX)
    (by simpa only [qY, qX, qO, qE, Iso.app_inv, Category.assoc] using
      zariskiInverseImagePullbackIso_integer_inv f)
    (moduleCoefficientComparison_pullback f M).symm n y
  have hv := zariskiCohomologyMap_valueLift f
    (Scheme.Cohomology.moduleAddSheaf Y M)
    (Scheme.Cohomology.moduleAddSheaf X ((Scheme.Modules.pullback f).obj M))
    (Scheme.Cohomology.moduleCoefficientPullback f
      ((pullbackPushforwardAdjunction f).unit.app M)) n x
  rw [← raisedModulePullback_eq_valueLift] at hv
  rw [Functor.extPrecompMap_compFunctor, Functor.extPrecompMap_compFunctor] at h
  rw [moduleCohomologyComparison_apply_adjunct]
  change (Ext.mk₀ qX.inv).comp
    (((valueLiftCohomologyMap.{u + 1, u + 2, u, u, u, u + 1} isTerminalTop
      (Scheme.Cohomology.moduleAddSheaf X ((Scheme.Modules.pullback f).obj M)) n
      (Scheme.Cohomology.zariskiCohomologyMap f
        (Scheme.Cohomology.moduleAddSheaf Y M)
        (Scheme.Cohomology.moduleAddSheaf X ((Scheme.Modules.pullback f).obj M))
        (Scheme.Cohomology.moduleCoefficientPullback f
          ((pullbackPushforwardAdjunction f).unit.app M)) n x)).mapExactFunctor
        (zariskiInverseImage X)).comp (Ext.mk₀ aX) (Nat.add_zero n)) (Nat.zero_add n) = _
  rw [hv]
  rw [moduleCohomologyComparison_apply_adjunct]
  change (Ext.mk₀ qX.inv).comp
      (((((Opens.map f.base).sheafPullback AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).extPrecompMap
          qO.inv _ n y).comp (Ext.mk₀ c) (Nat.add_zero n)).mapExactFunctor
            (zariskiInverseImage X) |>.comp (Ext.mk₀ aX) (Nat.add_zero n))
        (Nat.zero_add n) =
    (((inverseImage f).extPrecompMap qE.inv _ n
      ((Ext.mk₀ qY.inv).comp
        ((y.mapExactFunctor (zariskiInverseImage Y)).comp (Ext.mk₀ aY)
          (Nat.add_zero n)) (Nat.zero_add n))).comp (Ext.mk₀ b) (Nat.add_zero n))
  simpa only [Functor.extPrecompMap_apply, Ext.comp_mapExactFunctor,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀] using h.symm

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
