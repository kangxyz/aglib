/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.OpenRestrictionSections
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# Localization of original direct-sum sections on affine opens

The direct sum of the original graded section modules commutes with affine
restriction. Each unit tensor is sent to the direct sum of the actual
presheaf restrictions, so this comparison can be used to glue graded modules
with an additional commuting scalar action.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings DirectSum

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (U V : X.affineOpens) (i : V.val ⟶ U.val)
  {δ : Type v} [DecidableEq δ] (M : δ → X.Modules) [∀ n, (M n).IsQuasicoherent]

/-- Actual direct-sum affine sections obey scalar extension along the
original coordinate-ring restriction. -/
def directSumAffineOpenRestrictionIso :
    (ModuleCat.extendScalars (X.presheaf.map i.op).hom).obj
      (ModuleCat.of Γ(X, U) (⨁ n, Γ(M n, U))) ≅
      ModuleCat.of Γ(X, V) (⨁ n, Γ(M n, V)) := by
  letI : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map i.op).hom.toAlgebra
  exact (TensorProduct.directSumRight Γ(X, U) Γ(X, V) Γ(X, V)
      (fun n => Γ(M n, U))).toModuleIso ≪≫
    (DirectSum.congrLinearEquiv
      (fun n => (affineOpenRestrictionSectionsIso U V i (M n)).toLinearEquiv)).toModuleIso

/-- Every homogeneous unit tensor maps to the original section restriction. -/
theorem directSumAffineOpenRestrictionIso_one_tmul_lof (n : δ) (m : Γ(M n, U)) :
    (directSumAffineOpenRestrictionIso U V i M).hom
      ((1 : Γ(X, V)) ⊗ₜ[Γ(X, U),(X.presheaf.map i.op).hom]
        DirectSum.lof Γ(X, U) δ (fun n => Γ(M n, U)) n m) =
      DirectSum.lof Γ(X, V) δ (fun n => Γ(M n, V)) n ((M n).val.map i.op m) := by
  let : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map i.op).hom.toAlgebra
  dsimp only [directSumAffineOpenRestrictionIso, Iso.trans_hom,
    LinearEquiv.toModuleIso, ModuleCat.comp_apply, ModuleCat.ofHom_apply]
  erw [ConcreteCategory.comp_apply, ModuleCat.ofHom_apply, ModuleCat.ofHom_apply]
  erw [TensorProduct.directSumRight_tmul_lof, DirectSum.coe_congrLinearEquiv,
    DirectSum.lmap_lof]
  exact congrArg (DirectSum.lof Γ(X, V) δ (fun n => Γ(M n, V)) n)
    (affineOpenRestrictionSectionsIso_one_tmul U V i (M n) m)

end AlgebraicGeometry.Scheme.Modules
