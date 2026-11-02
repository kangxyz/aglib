/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Free.Sections

/-! # Original affine frame values through a section-class dictionary

The full original tilde comparison, frame map and class dictionary are kept
variable before a resolution or derived coefficient is substituted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u v

/-- The complete affine frame sends the original class representative to its
original ring coordinate. The supplied frame equation is an equation of the
actual sheaf arrows, not a replacement model or a desired value law. -/
theorem tildeFrame_class (R : CommRingCat.{u}) (M : ModuleCat.{u} R)
    (N : (Spec R).Modules) (c : tilde M ≅ N) (P : M ≃ₗ[R] R)
    (F : N ⟶ SheafOfModules.unit (Spec R).ringCatSheaf)
    (hF : F = c.inv ≫ (tilde.functor R).map P.toModuleIso.hom ≫ (tildeSelf (R := R)).hom)
    {V : Type v} [AddCommGroup V] (E : M ≃+ V) (ξ : V) (r : R)
    (hξ : E (P.symm r) = ξ) (U : (Spec R).Opens) :
    F.val.app (op U) (c.hom.val.app (op U) (tilde.toOpen M U (E.symm ξ))) =
      tilde.toOpen (ModuleCat.of R R) U r := by
  have hx : E.symm ξ = P.symm r := by
    apply E.injective
    exact (E.apply_symm_apply ξ).trans hξ.symm
  have hP : P (E.symm ξ) = r := (congrArg P hx).trans (P.apply_symm_apply r)
  let t := tilde.toOpen M U (E.symm ξ)
  have hf := congrArg (fun z => z.val.app (op U) (c.hom.val.app (op U) t)) hF
  change F.val.app (op U) (c.hom.val.app (op U) t) =
    ((tilde.functor R).map P.toModuleIso.hom).val.app (op U)
      (c.inv.val.app (op U) (c.hom.val.app (op U) t)) at hf
  have hc := congrArg (fun z => z.val.app (op U) t) c.hom_inv_id
  have ht := ConcreteCategory.congr_hom (tilde.toOpen_map_app P.toModuleIso.hom U) (E.symm ξ)
  change ((tilde.functor R).map P.toModuleIso.hom).val.app (op U) t =
    tilde.toOpen (ModuleCat.of R R) U (P (E.symm ξ)) at ht
  exact hf.trans ((congrArg
    (((tilde.functor R).map P.toModuleIso.hom).val.app (op U)) hc).trans
      (ht.trans (congrArg (tilde.toOpen (ModuleCat.of R R) U) hP)))

end AlgebraicGeometry.Scheme.Modules
