/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Contraction

/-!
# Cancellation of the actual generator-change factors

The original generator-change law multiplies the top Koszul class by the
same determinant that multiplies the ordered normal wedge. Native tensor
balancing moves that factor from the dual section to the normal section.
Evaluation on the changed wedge is one, so the concrete contracted section
is unchanged. The argument needs no determinant-unit premise, and includes
the zero ring and the empty normal list.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible
open CategoryTheory.MonoidalCategory

universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (C : LineBundle X)
  (eC : C.val ≅ SheafOfModules.unit X.ringCatSheaf)
  (eD : (dualLineBundle X C).val ≅ SheafOfModules.unit X.ringCatSheaf)

/-- The original sheafification unit preserves the native balancing relation. -/
theorem normalDualTensorSection_balance (U : X.Opens) (a : Γ(X, U))
    (ell : (dualLineBundle X C).val.val.obj (op U))
    (c : C.val.val.obj (op U)) :
    moduleTensorSection X (dualLineBundle X C).val C.val U (a • ell) c =
      moduleTensorSection X (dualLineBundle X C).val C.val U ell (a • c) := by
  unfold moduleTensorSection SheafOfModulesOfCommRing.tensorSection
  exact congrArg
    (((SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app
      (((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj (dualLineBundle X C).val) ⊗
        ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj C.val))).app (op U))
    (TensorProduct.smul_tmul (R := X.sheaf.obj.obj (op U))
      (R' := X.sheaf.obj.obj (op U)) (show X.sheaf.obj.obj (op U) from a) ell c)

/-- The top-class determinant factor cancels the same normal-wedge determinant factor. -/
theorem normalDeterminantContractionIso_generator_factor {Q P : X.Modules}
    (Δ : tensorSheaf X C.val Q ≅ P) (U : X.Opens) (a : Γ(X, U))
    (ell : (dualLineBundle X C).val.val.obj (op U))
    (c c' : C.val.val.obj (op U)) (q : Q.val.obj (op U))
    (hc : c' = a • c)
    (h : (dualEvaluationIso X C).hom.val.app (op U)
      (moduleTensorSection X (dualLineBundle X C).val C.val U ell c') =
        (1 : Γ(X, U))) :
    (normalDeterminantContractionIso C eC eD Δ).hom.val.app (op U)
      (moduleTensorSection X (dualLineBundle X C).val P U (a • ell)
        (Δ.hom.val.app (op U) (moduleTensorSection X C.val Q U c q))) = q := by
  apply normalDeterminantContractionIso_section_one
  rw [normalDualTensorSection_balance, ← hc]
  exact h

end AlgebraicGeometry.Scheme.Modules
