/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Contraction

/-!
# Inserting the same ordered normal generator

The normal unit frame inserts its own inverse generator before the tangent
factor and then applies the original normal-first determinant. Native dual
evaluation equal to one makes this insertion inverse to contraction on
the same pure section.
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

/-- Insert the generator of the original normal unit frame and apply the same determinant. -/
def normalDeterminantInsertionIso {Q P : X.Modules}
    (Δ : tensorSheaf X C.val Q ≅ P) : Q ≅ P :=
  ((((SheafOfModulesOfCommRing.tensorFunctor X.sheaf).mapIso eC).app Q ≪≫
    (SheafOfModulesOfCommRing.tensorLeftUnitIso X.sheaf).app Q).symm) ≪≫ Δ

/-- The actual insertion inserts the same normal section evaluating to one in its frame. -/
theorem normalDeterminantInsertionIso_section {Q P : X.Modules}
    (Δ : tensorSheaf X C.val Q ≅ P) (U : X.Opens)
    (c : C.val.val.obj (op U)) (q : Q.val.obj (op U))
    (hc : eC.hom.val.app (op U) c = (1 : Γ(X, U))) :
    (normalDeterminantInsertionIso C eC Δ).hom.val.app (op U) q =
      Δ.hom.val.app (op U) (moduleTensorSection X C.val Q U c q) := by
  let a := ((SheafOfModulesOfCommRing.tensorFunctor X.sheaf).mapIso eC).app Q ≪≫
    (SheafOfModulesOfCommRing.tensorLeftUnitIso X.sheaf).app Q
  let z := moduleTensorSection X C.val Q U c q
  have ha : a.hom.val.app (op U) z = q :=
    (tensorToUnit_section eC.hom Q U c q).trans
      ((congrArg (fun r : Γ(X, U) => r • q) hc).trans (one_smul Γ(X, U) q))
  have hi : a.inv.val.app (op U) q = z :=
    (congrArg (a.inv.val.app (op U)) ha.symm).trans
      (congrArg (fun f => f.val.app (op U) z) a.hom_inv_id)
  exact congrArg (Δ.hom.val.app (op U)) hi

/-- The same dual section of evaluation one contracts any coefficient section to the
inverse of the actual insertion isomorphism. -/
theorem normalDeterminantContractionIso_eq_insertion_inv
    (eD : (dualLineBundle X C).val ≅ SheafOfModules.unit X.ringCatSheaf)
    {Q P : X.Modules} (Δ : tensorSheaf X C.val Q ≅ P) (U : X.Opens)
    (ell : (dualLineBundle X C).val.val.obj (op U))
    (c : C.val.val.obj (op U)) (p : P.val.obj (op U))
    (hc : eC.hom.val.app (op U) c = (1 : Γ(X, U)))
    (he : (dualEvaluationIso X C).hom.val.app (op U)
      (moduleTensorSection X (dualLineBundle X C).val C.val U ell c) =
        (1 : Γ(X, U))) :
    (normalDeterminantContractionIso C eC eD Δ).hom.val.app (op U)
        (moduleTensorSection X (dualLineBundle X C).val P U ell p) =
      (normalDeterminantInsertionIso C eC Δ).inv.val.app (op U) p := by
  let I := normalDeterminantInsertionIso C eC Δ
  let q := I.inv.val.app (op U) p
  have hp : Δ.hom.val.app (op U) (moduleTensorSection X C.val Q U c q) = p :=
    (normalDeterminantInsertionIso_section C eC Δ U c q hc).symm.trans
      (congrArg (fun f => f.val.app (op U) p) I.inv_hom_id)
  exact (congrArg ((normalDeterminantContractionIso C eC eD Δ).hom.val.app (op U))
    (congrArg (moduleTensorSection X (dualLineBundle X C).val P U ell) hp).symm).trans
      (normalDeterminantContractionIso_section_one C eC eD Δ U ell c q he)

/-- Contraction followed by insertion retains the original coefficient section. -/
theorem normalDeterminantContractionIso_insert_section
    (eD : (dualLineBundle X C).val ≅ SheafOfModules.unit X.ringCatSheaf)
    {Q P : X.Modules} (Δ : tensorSheaf X C.val Q ≅ P) (U : X.Opens)
    (ell : (dualLineBundle X C).val.val.obj (op U))
    (c : C.val.val.obj (op U)) (p : P.val.obj (op U))
    (hc : eC.hom.val.app (op U) c = (1 : Γ(X, U)))
    (he : (dualEvaluationIso X C).hom.val.app (op U)
      (moduleTensorSection X (dualLineBundle X C).val C.val U ell c) =
        (1 : Γ(X, U))) :
    (normalDeterminantInsertionIso C eC Δ).hom.val.app (op U)
      ((normalDeterminantContractionIso C eC eD Δ).hom.val.app (op U)
        (moduleTensorSection X (dualLineBundle X C).val P U ell p)) = p :=
  (congrArg ((normalDeterminantInsertionIso C eC Δ).hom.val.app (op U))
    (normalDeterminantContractionIso_eq_insertion_inv C eC eD Δ U ell c p hc he)).trans
      (congrArg (fun f => f.val.app (op U) p)
        (normalDeterminantInsertionIso C eC Δ).inv_hom_id)

end AlgebraicGeometry.Scheme.Modules
