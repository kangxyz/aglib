/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.RestrictionSections

/-! # Original restrictions between commuting affine charts -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {X : Scheme.{u}} {R S : CommRingCat.{u}} (φ : R ⟶ S)
  (a : Spec R ⟶ X) (b : Spec S ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion (Spec.map φ)]
  (h : Spec.map φ ≫ a = b) (M : X.Modules)

omit [IsOpenImmersion (Spec.map φ)] in
include h in
/-- The original chart factorization gives inclusion of the actual chart images. -/
theorem affineChart_image_le : b ''ᵁ (⊤ : (Spec S).Opens) ≤ a ''ᵁ (⊤ : (Spec R).Opens) := by
  rintro _ ⟨z, _, rfl⟩
  exact ⟨Spec.map φ z, trivial, congrArg (fun k => k z) h⟩

/-- The actual composite restriction is identified with the specified smaller chart. -/
def affineChartRestrictionIso :
    (M.restrict a).restrict (Spec.map φ) ≅ M.restrict b :=
  (restrictFunctorComp (Spec.map φ) a).symm.app M ≪≫
    (restrictFunctorCongr h).app M

/-- The native restriction unit and chart rebracketing give the original
presheaf restriction on sections, without a quasicoherence hypothesis. -/
theorem affineChartRestrictionIso_unit
    (x : moduleSpecΓFunctor.obj (M.restrict a)) :
    (moduleSpecΓFunctor.map (affineChartRestrictionIso φ a b h M).hom)
      ((pushforwardGlobalSectionsIso φ).hom.app ((M.restrict a).restrict (Spec.map φ))
        (moduleSpecΓFunctor.map ((restrictAdjunction (Spec.map φ)).unit.app (M.restrict a)) x)) =
      M.presheaf.map (homOfLE (affineChart_image_le φ a b h)).op x := by
  change (((restrictFunctorCongr h).hom.app M).app ⊤)
    ((((restrictFunctorComp (Spec.map φ) a).inv.app M).app ⊤)
      ((((restrictAdjunction (Spec.map φ)).unit.app (M.restrict a)).app ⊤) x)) = _
  rw [restrictFunctorCongr_hom_app_app, restrictFunctorComp_inv_app_app,
    restrictAdjunction_unit_app_app, restrict_map]
  change M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ x)) =
    M.presheaf.map _ x
  simp only [← Functor.map_comp_apply]
  congr 1

end AlgebraicGeometry.Scheme.Modules
