/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.NativeFrameClass

/-! # Shared native model section of an affine class

The original model inverse, tilde counit and class dictionary construct one
section before specializing a concrete derived object or Ext representative.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u v

/-- The original class section through its native model inverse and affine counit. -/
def nativeFrameModelSection (R : CommRingCat.{u}) {M : ModuleCat.{u} R}
    {N Q : (Spec R).Modules} (E : Q ≅ N) (c : tilde M ≅ N)
    {V : Type v} [AddCommGroup V] (D : M ≃+ V) (ξ : V)
    (U : (Spec R).Opens) : Q.val.obj (op U) :=
  E.inv.val.app (op U) (c.hom.val.app (op U) (tilde.toOpen M U (D.symm ξ)))

/-- Compare an original native section with its original affine model class,
using the whole native/model frame factorization and the same class dictionary. -/
theorem nativeFrame_class_eq_section (R : CommRingCat.{u}) (M : ModuleCat.{u} R)
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
    x = nativeFrameModelSection R E' c D' ξ U := by
  exact nativeFrame_class_eq R M N Q E E' hE c P F hF K hK D D' hD ξ r hξ U x hx

end AlgebraicGeometry.Scheme.Modules
