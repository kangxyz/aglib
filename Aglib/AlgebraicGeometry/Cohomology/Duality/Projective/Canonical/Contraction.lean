/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorFunctorAssociator.Sections
public import Aglib.AlgebraicGeometry.Modules.Tensor.ToUnit

/-!
# Contraction of the actual normal determinant

The normal-first determinant is contracted by its inverse, the original
sheafified tensor associator, and native dual evaluation. The displayed
unit frames prove that the prescribed associator is invertible; they do not
replace any of its maps. The third tensor factor can be any module sheaf.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (C : LineBundle X)
  (eC : C.val ≅ SheafOfModules.unit X.ringCatSheaf)
  (eD : (dualLineBundle X C).val ≅ SheafOfModules.unit X.ringCatSheaf)

/-- The original tensor associator on the dual normal line and the normal line. -/
def normalDeterminantTensorAssociator :
    moduleTensorLeftFunctor X C.val ⋙
        moduleTensorLeftFunctor X (dualLineBundle X C).val ≅
      moduleTensorLeftFunctor X
        (tensorSheaf X (dualLineBundle X C).val C.val) :=
  moduleLineTensorAssociator (dualLineBundle X C).val C.val
    (fun _ : PUnit.{1} => X) (fun _ => 𝟙 X)
    (fun x => ⟨PUnit.unit, x, rfl⟩)
    (fun _ => restrictFunctorId.app _ ≪≫ eD)
    (fun _ => restrictFunctorId.app _ ≪≫ eC)

/-- Contract the inverse of the same normal-first determinant using native dual evaluation. -/
def normalDeterminantContractionIso {Q P : X.Modules}
    (Δ : tensorSheaf X C.val Q ≅ P) :
    tensorSheaf X (dualLineBundle X C).val P ≅ Q :=
  (moduleTensorLeftFunctor X (dualLineBundle X C).val).mapIso Δ.symm ≪≫
    (normalDeterminantTensorAssociator C eC eD).app Q ≪≫
    ((SheafOfModulesOfCommRing.tensorFunctor X.sheaf).mapIso
      (dualEvaluationIso X C)).app Q ≪≫
    (SheafOfModulesOfCommRing.tensorLeftUnitIso X.sheaf).app Q

/-- On the same ordered normal/tangent tensor the contraction is its native evaluation.
This is an equation of the actual sheaf arrow on the original tensor sections. -/
theorem normalDeterminantContractionIso_section {Q P : X.Modules}
    (Δ : tensorSheaf X C.val Q ≅ P) (U : X.Opens)
    (ell : (dualLineBundle X C).val.val.obj (op U))
    (c : C.val.val.obj (op U)) (q : Q.val.obj (op U)) :
    (normalDeterminantContractionIso C eC eD Δ).hom.val.app (op U)
      (moduleTensorSection X (dualLineBundle X C).val P U ell
        (Δ.hom.val.app (op U) (moduleTensorSection X C.val Q U c q))) =
      (show Γ(X, U) from (dualEvaluationIso X C).hom.val.app (op U)
        (moduleTensorSection X (dualLineBundle X C).val C.val U ell c)) • q := by
  let z := moduleTensorSection X C.val Q U c q
  have hΔ : Δ.inv.val.app (op U) (Δ.hom.val.app (op U) z) = z :=
    congrArg (fun f => f.val.app (op U) z) Δ.hom_inv_id
  change ((tensorToUnit (dualEvaluationIso X C).hom).app Q).val.app (op U)
    (((normalDeterminantTensorAssociator C eC eD).hom.app Q).val.app (op U)
      (((moduleTensorLeftFunctor X (dualLineBundle X C).val).map Δ.inv).val.app (op U)
        (moduleTensorSection X (dualLineBundle X C).val P U ell
          (Δ.hom.val.app (op U) z)))) = _
  have hmap := moduleTensorLeftFunctor_map_section (dualLineBundle X C).val Δ.inv U ell
    (Δ.hom.val.app (op U) z)
  change (((moduleTensorLeftFunctor X (dualLineBundle X C).val).map Δ.inv).val.app (op U))
      (moduleTensorSection X (dualLineBundle X C).val P U ell (Δ.hom.val.app (op U) z)) =
    moduleTensorSection X (dualLineBundle X C).val (tensorSheaf X C.val Q) U ell
      (Δ.inv.val.app (op U) (Δ.hom.val.app (op U) z)) at hmap
  have hcancel := hmap.trans (congrArg
    (moduleTensorSection X (dualLineBundle X C).val (tensorSheaf X C.val Q) U ell) hΔ)
  have hassoc : ((normalDeterminantTensorAssociator C eC eD).hom.app Q).val.app (op U)
      (moduleTensorSection X (dualLineBundle X C).val
        (tensorSheaf X C.val Q) U ell z) =
      moduleTensorSection X (tensorSheaf X (dualLineBundle X C).val C.val) Q U
        (moduleTensorSection X (dualLineBundle X C).val C.val U ell c) q :=
    moduleLineTensorAssociator_hom_section (dualLineBundle X C).val C.val
      (fun _ : PUnit.{1} => X) (fun _ => 𝟙 X)
      (fun x => ⟨PUnit.unit, x, rfl⟩)
      (fun _ => restrictFunctorId.app _ ≪≫ eD)
      (fun _ => restrictFunctorId.app _ ≪≫ eC) Q U ell c q
  exact (congrArg (fun t => ((tensorToUnit (dualEvaluationIso X C).hom).app Q).val.app (op U)
    (((normalDeterminantTensorAssociator C eC eD).hom.app Q).val.app (op U) t)) hcancel).trans
      ((congrArg (((tensorToUnit (dualEvaluationIso X C).hom).app Q).val.app (op U))
        hassoc).trans (tensorToUnit_section (dualEvaluationIso X C).hom Q U _ q))

/-- A dual generator evaluating to one cancels the same ordered normal wedge. -/
theorem normalDeterminantContractionIso_section_one {Q P : X.Modules}
    (Δ : tensorSheaf X C.val Q ≅ P) (U : X.Opens)
    (ell : (dualLineBundle X C).val.val.obj (op U))
    (c : C.val.val.obj (op U)) (q : Q.val.obj (op U))
    (h : (dualEvaluationIso X C).hom.val.app (op U)
      (moduleTensorSection X (dualLineBundle X C).val C.val U ell c) =
        (1 : Γ(X, U))) :
    (normalDeterminantContractionIso C eC eD Δ).hom.val.app (op U)
      (moduleTensorSection X (dualLineBundle X C).val P U ell
        (Δ.hom.val.app (op U) (moduleTensorSection X C.val Q U c q))) = q := by
  rw [normalDeterminantContractionIso_section, h, one_smul]

/-- Unit frames only establish invertibility of the prescribed tensor maps. -/
theorem normalDeterminantContractionIso_independent_frames {Q P : X.Modules}
    (Δ : tensorSheaf X C.val Q ≅ P)
    (eC' : C.val ≅ SheafOfModules.unit X.ringCatSheaf)
    (eD' : (dualLineBundle X C).val ≅ SheafOfModules.unit X.ringCatSheaf) :
    normalDeterminantContractionIso C eC eD Δ =
      normalDeterminantContractionIso C eC' eD' Δ := by
  rfl

end AlgebraicGeometry.Scheme.Modules
