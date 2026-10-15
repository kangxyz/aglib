/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.RestrictionSections
public import Aglib.Algebra.Category.ModuleCat.ScalarExtensionUnit
/-! # Affine restriction with explicit coefficient rings

The original open-restriction adjunction unit is compared with scalar extension.
All three ring maps and their compatibility remain explicit.
-/

@[expose] public section

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry ModuleCat
namespace AlgebraicGeometry.Scheme.Modules
variable {R A S : CommRingCat.{u}} (a : R ⟶ A) (φ : A ⟶ S) (c : R ⟶ S)
  (h : c.hom = φ.hom.comp a.hom) [IsOpenImmersion (Spec.map φ)]

/-- The original affine open-restriction unit with coefficients restricted to the base ring. -/
def coefficientRestrictionMap (M : (Spec A).Modules) :
    (restrictScalars a.hom).obj (moduleSpecΓFunctor.obj M) ⟶
      (restrictScalars c.hom).obj (moduleSpecΓFunctor.obj (M.restrict (Spec.map φ))) :=
  (restrictScalars a.hom).map
    (moduleSpecΓFunctor.map ((Scheme.Modules.restrictAdjunction (Spec.map φ)).unit.app M) ≫
      (pushforwardGlobalSectionsIso φ).hom.app (M.restrict (Spec.map φ))) ≫
    (restrictScalarsComp'App a.hom φ.hom c.hom h
      (moduleSpecΓFunctor.obj (M.restrict (Spec.map φ)))).inv

/-- For a quasicoherent sheaf, the original restriction unit is the scalar-extension unit. -/
theorem coefficientRestrictionMap_eq (M : (Spec A).Modules) [M.IsQuasicoherent] :
    coefficientRestrictionMap a φ c h M =
      restrictedExtensionUnit a.hom φ.hom c.hom h (moduleSpecΓFunctor.obj M) ≫
        (restrictScalars c.hom).map (affineRestrictGlobalSectionsIso φ M).hom := by
  rw [coefficientRestrictionMap, ← affineRestrictGlobalSectionsIso_unit]
  simp only [Functor.map_comp, Category.assoc, restrictedExtensionUnit]
  rw [restrictScalarsComp'App_inv_naturality]

end AlgebraicGeometry.Scheme.Modules
end

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry ModuleCat
namespace AlgebraicGeometry.Scheme.Modules
variable {R A S : CommRingCat.{u}} (a : R ⟶ A) (φ : A ⟶ S) (c : R ⟶ S)
  (h : c.hom = φ.hom.comp a.hom) [IsOpenImmersion (Spec.map φ)]

/-- The coefficient restriction map acts by the original sheaf adjunction unit on top sections. -/
theorem coefficientRestrictionMap_apply (M : (Spec A).Modules)
    (x : (restrictScalars a.hom).obj (moduleSpecΓFunctor.obj M)) :
    coefficientRestrictionMap a φ c h M x =
      (((Scheme.Modules.restrictAdjunction (Spec.map φ)).unit.app M).app ⊤) x := rfl

end AlgebraicGeometry.Scheme.Modules
end

end
