/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Refinement

/-! # Pasting coefficient comparisons through cartesian chart refinement -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The original refinement square between two local comparisons. -/
def RestrictionComparisonSquare
    {X U V : Scheme.{u}} (jU : U ⟶ X) (jV : V ⟶ X) (k : V ⟶ U)
    [IsOpenImmersion jU] [IsOpenImmersion jV] [IsOpenImmersion k]
    (hj : k ≫ jU = jV) (N M : X.Modules)
    (eU : N.restrict jU ⟶ M.restrict jU)
    (eV : N.restrict jV ⟶ M.restrict jV) : Prop :=
  (restrictFunctor k).map eU ≫
      ((restrictFunctorComp k jU).symm.app M ≪≫ (restrictFunctorCongr hj).app M).hom =
    ((restrictFunctorComp k jU).symm.app N ≪≫ (restrictFunctorCongr hj).app N).hom ≫ eV

/-- Compatible local coefficient and pushforward comparisons give the original
refinement square for a realized coefficient. -/
theorem cartesianOpenBaseChange_refinement_comparison
    {Y X U V WU WV : Scheme.{u}} (p : Y ⟶ X)
    (jU : U ⟶ X) (jV : V ⟶ X) (k : V ⟶ U)
    (cU : WU ⟶ Y) (cV : WV ⟶ Y) (t : WV ⟶ WU)
    (pU : WU ⟶ U) (pV : WV ⟶ V)
    [IsOpenImmersion jU] [IsOpenImmersion jV] [IsOpenImmersion k]
    [IsOpenImmersion cU] [IsOpenImmersion cV] [IsOpenImmersion t]
    (hj : k ≫ jU = jV) (hc : t ≫ cU = cV)
    (HU : IsPullback cU pU p jU) (HV : IsPullback cV pV p jV)
    (HW : IsPullback t pV pU k)
    (G : Y.Modules) (M : X.Modules) (QU : WU.Modules) (QV : WV.Modules)
    (eU : G.restrict cU ≅ QU) (eV : G.restrict cV ≅ QV)
    (d : QU.restrict t ≅ QV)
    (vU : (pushforward pU).obj QU ≅ M.restrict jU)
    (vV : (pushforward pV).obj QV ≅ M.restrict jV)
    (he : (restrictFunctor t).map eU.hom ≫ d.hom =
      ((restrictFunctorComp t cU).symm.app G ≪≫ (restrictFunctorCongr hc).app G).hom ≫ eV.hom)
    (hv : (restrictFunctor k).map vU.hom ≫
        ((restrictFunctorComp k jU).symm.app M ≪≫ (restrictFunctorCongr hj).app M).hom =
      (cartesianOpenBaseChange t pV pU k HW).hom.app QU ≫
        (pushforward pV).map d.hom ≫ vV.hom) :
    RestrictionComparisonSquare jU jV k hj ((pushforward p).obj G) M
      ((cartesianOpenBaseChange cU pU p jU HU).app G ≪≫
        (pushforward pU).mapIso eU ≪≫ vU).hom
      ((cartesianOpenBaseChange cV pV p jV HV).app G ≪≫
        (pushforward pV).mapIso eV ≪≫ vV).hom := by
  unfold RestrictionComparisonSquare
  have hn := (cartesianOpenBaseChange t pV pU k HW).hom.naturality eU.hom
  dsimp only [Functor.comp_map] at hn
  dsimp only [Iso.trans_hom, Iso.app_hom] at hv
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [hv]
  rw [← Category.assoc ((restrictFunctor k).map ((pushforward pU).map eU.hom)), hn]
  simp only [Category.assoc]
  rw [← (pushforward pV).map_comp_assoc, he, Functor.map_comp]
  have hb := cartesianOpenBaseChange_refinement p jU jV k cU cV t pU pV hj hc HU HV HW G
  simpa only [Iso.trans_hom, Iso.app_hom, Category.assoc] using congrArg
    (fun q => q ≫ (pushforward pV).map eV.hom ≫ vV.hom) hb

end AlgebraicGeometry.Scheme.Modules
