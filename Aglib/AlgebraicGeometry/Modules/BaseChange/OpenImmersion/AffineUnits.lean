/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.CartesianSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pushforward

/-! # Original affine section units under cartesian open base change -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- On original affine sections, the actual open base-change comparison carries
the base restriction unit to the source restriction unit. -/
theorem cartesianOpenBaseChange_affine_unit
    {R S R' S' : CommRingCat.{u}} (pU : R ⟶ S) (pV : R' ⟶ S')
    (φ : R ⟶ R') (ψ : S ⟶ S')
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (H : IsPullback (Spec.map ψ) (Spec.map pV) (Spec.map pU) (Spec.map φ))
    (M : (Spec S).Modules) (x : moduleSpecΓFunctor.obj M) :
    (pushforwardGlobalSectionsIso pV).hom.app (M.restrict (Spec.map ψ))
        (moduleSpecΓFunctor.map
          ((cartesianOpenBaseChange (Spec.map ψ) (Spec.map pV) (Spec.map pU)
            (Spec.map φ) H).hom.app M)
          (moduleSpecΓFunctor.map ((restrictAdjunction (Spec.map φ)).unit.app
            ((pushforward (Spec.map pU)).obj M))
            ((pushforwardGlobalSectionsIso pU).inv.app M x))) =
      (pushforwardGlobalSectionsIso ψ).hom.app (M.restrict (Spec.map ψ))
        (moduleSpecΓFunctor.map ((restrictAdjunction (Spec.map ψ)).unit.app M) x) := by
  change (((cartesianOpenBaseChange (Spec.map ψ) (Spec.map pV) (Spec.map pU)
      (Spec.map φ) H).hom.app M).app ⊤)
      ((((restrictAdjunction (Spec.map φ)).unit.app
        ((pushforward (Spec.map pU)).obj M)).app ⊤) x) =
    (((restrictAdjunction (Spec.map ψ)).unit.app M).app ⊤) x
  rw [cartesianOpenBaseChange_hom_app, restrictAdjunction_unit_app_app,
    restrictAdjunction_unit_app_app, pushforward_obj_presheaf_map]
  change M.presheaf.map _ (M.presheaf.map _ x) = M.presheaf.map _ x
  simp only [← Functor.map_comp_apply]
  congr 1

end AlgebraicGeometry.Scheme.Modules
