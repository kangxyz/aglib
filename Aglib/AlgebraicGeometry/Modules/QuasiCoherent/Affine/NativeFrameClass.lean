/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FrameSections

/-! # Original native frame comparison of affine class representatives

A native section and its original model representative are compared through
one actual native frame. Model and class-dictionary equalities are transported
before specializing the original derived coefficient.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u v

/-- Compare an original native section with its original affine model class,
using the whole native/model frame factorization and the same class dictionary. -/
theorem nativeFrame_class_eq (R : CommRingCat.{u}) (M : ModuleCat.{u} R)
    (N Q : (Spec R).Modules) (E E' : Q ≅ N) (hE : E = E')
    (c : tilde M ≅ N) (P : M ≃ₗ[R] R)
    (F : N ⟶ SheafOfModules.unit (Spec R).ringCatSheaf)
    (hF : F = c.inv ≫ (tilde.functor R).map P.toModuleIso.hom ≫ (tildeSelf (R := R)).hom)
    (K : Q ≅ SheafOfModules.unit (Spec R).ringCatSheaf)
    (hK : K.hom = E.hom ≫ F)
    {V : Type v} [AddCommGroup V] (D D' : M ≃+ V) (hD : D = D')
    (ξ : V) (r : R) (hξ : D (P.symm r) = ξ)
    (U : (Spec R).Opens) (x : Q.val.obj (op U))
    (hx : K.hom.val.app (op U) x = tilde.toOpen (ModuleCat.of R R) U r) :
    x = E'.inv.val.app (op U)
      (c.hom.val.app (op U) (tilde.toOpen M U (D'.symm ξ))) := by
  subst E' D'
  let y := c.hom.val.app (op U) (tilde.toOpen M U (D.symm ξ))
  have hy := tildeFrame_class R M N c P F hF D ξ r hξ U
  have hcancel := congrArg (fun f => f.val.app (op U) y) E.inv_hom_id
  have hk := congrArg (fun f => f.val.app (op U) (E.inv.val.app (op U) y)) hK
  change K.hom.val.app (op U) (E.inv.val.app (op U) y) =
    F.val.app (op U) (E.hom.val.app (op U) (E.inv.val.app (op U) y)) at hk
  have hr := hk.trans ((congrArg (F.val.app (op U)) hcancel).trans hy)
  have h := hx.trans hr.symm
  have hleft := congrArg (fun f => f.val.app (op U) x) K.hom_inv_id
  have hright := congrArg (fun f => f.val.app (op U) (E.inv.val.app (op U) y))
    K.hom_inv_id
  exact hleft.symm.trans ((congrArg (K.inv.val.app (op U)) h).trans hright)

end AlgebraicGeometry.Scheme.Modules
