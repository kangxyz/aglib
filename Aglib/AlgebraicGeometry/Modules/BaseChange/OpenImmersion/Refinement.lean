/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.CartesianSections

/-! # Cartesian open base change under chart refinement -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The original cartesian open base-change maps commute with simultaneous
refinement of the source and target charts. -/
theorem cartesianOpenBaseChange_refinement
    {Y X U V WU WV : Scheme.{u}} (p : Y ⟶ X)
    (jU : U ⟶ X) (jV : V ⟶ X) (k : V ⟶ U)
    (cU : WU ⟶ Y) (cV : WV ⟶ Y) (t : WV ⟶ WU)
    (pU : WU ⟶ U) (pV : WV ⟶ V)
    [IsOpenImmersion jU] [IsOpenImmersion jV] [IsOpenImmersion k]
    [IsOpenImmersion cU] [IsOpenImmersion cV] [IsOpenImmersion t]
    (hj : k ≫ jU = jV) (hc : t ≫ cU = cV)
    (HU : IsPullback cU pU p jU) (HV : IsPullback cV pV p jV)
    (HW : IsPullback t pV pU k) (G : Y.Modules) :
    (restrictFunctor k).map ((cartesianOpenBaseChange cU pU p jU HU).hom.app G) ≫
        (cartesianOpenBaseChange t pV pU k HW).hom.app (G.restrict cU) ≫
        (pushforward pV).map
          (((restrictFunctorComp t cU).symm.app G ≪≫
            (restrictFunctorCongr hc).app G).hom) =
      ((restrictFunctorComp k jU).symm.app ((pushforward p).obj G) ≪≫
        (restrictFunctorCongr hj).app ((pushforward p).obj G)).hom ≫
          (cartesianOpenBaseChange cV pV p jV HV).hom.app G := by
  apply Scheme.Modules.hom_ext
  intro T
  simp only [Scheme.Modules.Hom.comp_app, restrictFunctor_map_app,
    Scheme.Modules.pushforward_map_app, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, cartesianOpenBaseChange_hom_app,
    restrictFunctorComp_inv_app_app, restrictFunctorCongr_hom_app_app,
    restrict_map, pushforward_obj_presheaf_map]
  simp only [← Functor.map_comp]
  congr 1

end AlgebraicGeometry.Scheme.Modules
