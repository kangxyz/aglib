/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.AnticanonicalHilbert.Geometric
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.Generation.VeryAmple
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.Serre.Field
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.QuasiCoherent

/-!
# Anticanonical Hilbert numerics along an algebraic extension

The original chosen projective pullback transports ordinary cohomology and
actual line powers. A genuine algebraically closed extension supplies the
regular hyperplane, and the original base-change maps descend every H0
rank. The extension is a variable input, not a chosen algebraic closure;
no new canonical module or canonical-module gluing is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Hom

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

private theorem cmCurveCohomology_subsingleton_fieldExtension
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (ι : Type u) [Finite ι] {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (M : C.Modules) [M.IsQuasicoherent] (r : ℕ)
    [Subsingleton (cmCurveSerreCohomology k ι j M r)] :
    Subsingleton (cmCurveSerreCohomology K ι
      (Limits.pullback.snd j (ProjectiveSpace.map (algebraMap k K) ι))
      ((Modules.pullback
        (Limits.pullback.fst j (ProjectiveSpace.map (algebraMap k K) ι))).obj M) r) :=
  cmCurveCohomologyFieldExtension_subsingleton k K ι j M r

-- This elementary line comparison only uses the original tensor and unit
-- pullbacks. It is not base change of a selected canonical module.
private def cmCurveHyperplaneDualFieldExtensionIso
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (ι : Type u) {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι) :
    let p := Limits.pullback.fst j (ProjectiveSpace.map (algebraMap k K) ι)
    let jK := Limits.pullback.snd j (ProjectiveSpace.map (algebraMap k K) ι)
    (Modules.pullback p).obj (dualLineBundle C (curveHyperplaneLine k ι j)).val ≅
      (dualLineBundle _ (curveHyperplaneLine K ι jK)).val := by
  let p := Limits.pullback.fst j (ProjectiveSpace.map (algebraMap k K) ι)
  let jK := Limits.pullback.snd j (ProjectiveSpace.map (algebraMap k K) ι)
  let CK := Limits.pullback j (ProjectiveSpace.map (algebraMap k K) ι)
  let L := curveHyperplaneLine k ι j
  let LK := curveHyperplaneLine K ι jK
  let U := (Modules.pullback p).obj (dualLineBundle C L).val
  let DK := (dualLineBundle CK LK).val
  let eL : (Modules.pullback p).obj L.val ≅ LK.val :=
    cmCurveTwistingFieldExtensionIso k K ι j 1
  let e : tensorSheaf CK U LK.val ≅ SheafOfModules.unit CK.ringCatSheaf :=
    tensorSheafIso CK (Iso.refl U) eL.symm ≪≫
      (pullbackTensorMapIso p (dualLineBundle C L).val L.val).symm ≪≫
      (Modules.pullback p).mapIso (dualEvaluationIso C L) ≪≫ pullbackUnitIso p
  let v : tensorSheaf CK LK.val DK ≅ SheafOfModules.unit CK.ringCatSheaf :=
    tensorSheafBraiding CK LK.val DK ≪≫ dualEvaluationIso CK LK
  exact (rightUnitor (C := CK.Modules) U).symm ≪≫
    (tensorLeft U).mapIso v.symm ≪≫ (associator U LK.val DK).symm ≪≫
    (tensorRight DK).mapIso e ≪≫ leftUnitor DK

/-- The inverse-line cohomology determines the full very-ample Hilbert
function over every field. A finite regular divisor is constructed after
algebraic closure, and dimensions descend along the original ordinary
cohomology base-change map. No canonical gluing over the larger field is used. -/
theorem cmCurve_hyperplanePower_h0_finrank_of_algebraic_extension
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] [IsAlgClosed K] (ι : Type u) [Finite ι]
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (hCM : ∀ x : C, IsClosed ({x} : Set C) →
      ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
        IsSMulRegular (C.presheaf.stalk x) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (C.presheaf.stalk x))
    [Subsingleton (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (SheafOfModules.unit C.ringCatSheaf) 1)]
    [Subsingleton (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (dualLineBundle C (curveHyperplaneLine k ι j)).val 0)]
    (hO : Module.finrank k (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (SheafOfModules.unit C.ringCatSheaf) 0) = 1)
    (hJ : Module.finrank k (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (dualLineBundle C (curveHyperplaneLine k ι j)).val 1) = 1) (r : ℕ) :
    Module.finrank k (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (tensorPowerLineBundle C (curveHyperplaneLine k ι j) r).val 0) = 2 * r + 1 := by
  let CK := Limits.pullback j (ProjectiveSpace.map (algebraMap k K) ι)
  let p := Limits.pullback.fst j (ProjectiveSpace.map (algebraMap k K) ι)
  let jK := Limits.pullback.snd j (ProjectiveSpace.map (algebraMap k K) ι)
  let XK : FScheme K := Over.mk (jK ≫ toSpec K ι)
  let O := SheafOfModules.unit C.ringCatSheaf
  let OK := SheafOfModules.unit CK.ringCatSheaf
  let L := curveHyperplaneLine k ι j
  let J := dualLineBundle C L
  let LK := curveHyperplaneLine K ι jK
  let JK := dualLineBundle CK LK
  let : O.IsQuasicoherent := Modules.isQuasicoherent_unit C
  let : Subsingleton (cmCurveSerreCohomology k ι j O 1) :=
    inferInstanceAs (Subsingleton (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (SheafOfModules.unit C.ringCatSheaf) 1))
  let : J.val.IsQuasicoherent := lineBundle_isQuasicoherent J
  let : Subsingleton (cmCurveSerreCohomology k ι j J.val 0) :=
    inferInstanceAs (Subsingleton (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (dualLineBundle C (curveHyperplaneLine k ι j)).val 0))
  let eO : (Modules.pullback p).obj O ≅ OK := pullbackUnitIso p
  let eL : (Modules.pullback p).obj L.val ≅ LK.val :=
    cmCurveTwistingFieldExtensionIso k K ι j 1
  let eJ : (Modules.pullback p).obj J.val ≅ JK.val :=
    cmCurveHyperplaneDualFieldExtensionIso k K ι j
  have hOK : Module.finrank K (moduleCohomology K XK OK 0) = 1 :=
    (moduleCohomologyIso XK eO 0).finrank_eq.symm.trans
      ((cmCurveSerreCohomologyField_finrank K ι jK ((Modules.pullback p).obj O) 0).symm.trans
        ((cmCurveCohomology_finrank_fieldExtension k K ι j O 0).trans
          ((cmCurveSerreCohomologyField_finrank k ι j O 0).trans hO)))
  have hJK : Module.finrank K (moduleCohomology K XK JK.val 1) = 1 :=
    (moduleCohomologyIso XK eJ 1).finrank_eq.symm.trans
      ((cmCurveSerreCohomologyField_finrank K ι jK ((Modules.pullback p).obj J.val) 1).symm.trans
        ((cmCurveCohomology_finrank_fieldExtension k K ι j J.val 1).trans
          ((cmCurveSerreCohomologyField_finrank k ι j J.val 1).trans hJ)))
  let : Subsingleton (moduleCohomology K XK ((Modules.pullback p).obj O) 1) :=
    cmCurveCohomology_subsingleton_fieldExtension k K ι j O 1
  let : Subsingleton (moduleCohomology K XK OK 1) :=
    (moduleCohomologyIso XK eO 1).symm.injective.subsingleton
  let : Subsingleton (moduleCohomology K XK ((Modules.pullback p).obj J.val) 0) :=
    cmCurveCohomology_subsingleton_fieldExtension k K ι j J.val 0
  let : Subsingleton (moduleCohomology K XK JK.val 0) :=
    (moduleCohomologyIso XK eJ 0).symm.injective.subsingleton
  have hCMK := Scheme.closed_parameters_projective_algebraic_field_extension k K ι j hCM
  have hK := cmCurve_hyperplanePower_cohomology_of_isAlgClosed K ι jK hCMK hOK hJK r
  let P := tensorPowerLineBundle C L r
  let : P.val.IsQuasicoherent := lineBundle_isQuasicoherent P
  let eP : (Modules.pullback p).obj P.val ≅ (tensorPowerLineBundle CK LK r).val :=
    PowerPullback.pullbackPowerIso p L r ≪≫ TrivializedPower.powerIso CK eL r
  exact (cmCurveSerreCohomologyField_finrank k ι j P.val 0).symm.trans
    ((cmCurveCohomology_finrank_fieldExtension k K ι j P.val 0).symm.trans
      ((cmCurveSerreCohomologyField_finrank K ι jK ((Modules.pullback p).obj P.val) 0).trans
        ((moduleCohomologyIso XK eP 0).finrank_eq.trans hK.2)))

/-- Ordinary cohomology of the original unit, first power and line powers
descends the three-section Hilbert function without canonical base change. -/
theorem cmCurve_hyperplanePower_h0_finrank_of_firstPower_of_algebraic_extension
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] [IsAlgClosed K] (ι : Type u) [Finite ι]
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (hCM : ∀ x : C, IsClosed ({x} : Set C) →
      ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
        IsSMulRegular (C.presheaf.stalk x) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (C.presheaf.stalk x))
    [Subsingleton (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (SheafOfModules.unit C.ringCatSheaf) 1)]
    (hO : Module.finrank k (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (SheafOfModules.unit C.ringCatSheaf) 0) = 1)
    (hL : Module.finrank k (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (curveHyperplaneLine k ι j).val 0) = 3) (r : ℕ) :
    Module.finrank k (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (tensorPowerLineBundle C (curveHyperplaneLine k ι j) r).val 0) = 2 * r + 1 := by
  let CK := Limits.pullback j (ProjectiveSpace.map (algebraMap k K) ι)
  let p := Limits.pullback.fst j (ProjectiveSpace.map (algebraMap k K) ι)
  let jK := Limits.pullback.snd j (ProjectiveSpace.map (algebraMap k K) ι)
  let XK : FScheme K := Over.mk (jK ≫ toSpec K ι)
  let O := SheafOfModules.unit C.ringCatSheaf
  let OK := SheafOfModules.unit CK.ringCatSheaf
  let L := curveHyperplaneLine k ι j
  let LK := curveHyperplaneLine K ι jK
  let : O.IsQuasicoherent := Modules.isQuasicoherent_unit C
  let : Subsingleton (cmCurveSerreCohomology k ι j O 1) :=
    inferInstanceAs (Subsingleton (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (SheafOfModules.unit C.ringCatSheaf) 1))
  let : L.val.IsQuasicoherent := lineBundle_isQuasicoherent L
  let eO : (Modules.pullback p).obj O ≅ OK := pullbackUnitIso p
  let eL : (Modules.pullback p).obj L.val ≅ LK.val :=
    cmCurveTwistingFieldExtensionIso k K ι j 1
  have hOK : Module.finrank K (moduleCohomology K XK OK 0) = 1 :=
    (moduleCohomologyIso XK eO 0).finrank_eq.symm.trans
      ((cmCurveSerreCohomologyField_finrank K ι jK ((Modules.pullback p).obj O) 0).symm.trans
        ((cmCurveCohomology_finrank_fieldExtension k K ι j O 0).trans
          ((cmCurveSerreCohomologyField_finrank k ι j O 0).trans hO)))
  have hLK : Module.finrank K (moduleCohomology K XK LK.val 0) = 3 :=
    (moduleCohomologyIso XK eL 0).finrank_eq.symm.trans
      ((cmCurveSerreCohomologyField_finrank K ι jK ((Modules.pullback p).obj L.val) 0).symm.trans
        ((cmCurveCohomology_finrank_fieldExtension k K ι j L.val 0).trans
          ((cmCurveSerreCohomologyField_finrank k ι j L.val 0).trans hL)))
  let : Subsingleton (moduleCohomology K XK ((Modules.pullback p).obj O) 1) :=
    cmCurveCohomology_subsingleton_fieldExtension k K ι j O 1
  let : Subsingleton (moduleCohomology K XK OK 1) :=
    (moduleCohomologyIso XK eO 1).symm.injective.subsingleton
  have hCMK := Scheme.closed_parameters_projective_algebraic_field_extension k K ι j hCM
  have hK := cmCurve_hyperplanePower_cohomology_of_firstPower_of_isAlgClosed
    K ι jK hCMK hOK hLK r
  let P := tensorPowerLineBundle C L r
  let : P.val.IsQuasicoherent := lineBundle_isQuasicoherent P
  let eP : (Modules.pullback p).obj P.val ≅ (tensorPowerLineBundle CK LK r).val :=
    PowerPullback.pullbackPowerIso p L r ≪≫ TrivializedPower.powerIso CK eL r
  exact (cmCurveSerreCohomologyField_finrank k ι j P.val 0).symm.trans
    ((cmCurveCohomology_finrank_fieldExtension k K ι j P.val 0).symm.trans
      ((cmCurveSerreCohomologyField_finrank K ι jK ((Modules.pullback p).obj P.val) 0).trans
        ((moduleCohomologyIso XK eP 0).finrank_eq.trans hK.2)))


end AlgebraicGeometry.Scheme.Cohomology
