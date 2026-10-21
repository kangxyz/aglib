/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Restriction.Overlap
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.CartesianSections

/-! # Compatibility of restriction with a presentation of an overlap

Presenting the chosen categorical pullback by a cartesian chart does not change the
original comparison between the two restrictions of an ambient module.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The restriction comparison through any cartesian presentation of an overlap
is the canonical comparison on the chosen categorical pullback. -/
theorem overlapRestrictIso_refinement
    {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V)
    (j : U ⟶ X) (k : V ⟶ X) (c : W ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j]
    [IsOpenImmersion k] [IsOpenImmersion c]
    (H : IsPullback a b j k) (ha : a ≫ j = c) (hb : b ≫ k = c)
    (M : X.Modules) :
    let l := H.isoPullback.inv
    let rU := (restrictFunctorComp a j).symm.app M ≪≫
      (restrictFunctorCongr ha).app M
    let rV := (restrictFunctorComp b k).symm.app M ≪≫
      (restrictFunctorCongr hb).app M
    let eU := (restrictFunctorCongr H.isoPullback_inv_fst).symm.app (M.restrict j) ≪≫
      (restrictFunctorComp l a).app (M.restrict j)
    let eV := (restrictFunctorCongr H.isoPullback_inv_snd).symm.app (M.restrict k) ≪≫
      (restrictFunctorComp l b).app (M.restrict k)
    (eU ≪≫ (restrictFunctor l).mapIso (rU ≪≫ rV.symm) ≪≫ eV.symm).hom =
      (overlapRestrictIso j k).hom.app M := by
  dsimp only
  apply Scheme.Modules.hom_ext
  intro T
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, overlapRestrictIso,
    NatTrans.comp_app, Scheme.Modules.Hom.comp_app, restrictFunctor_map_app,
    restrictFunctorComp_hom_app_app, restrictFunctorComp_inv_app_app,
    restrictFunctorCongr_hom_app_app, restrictFunctorCongr_inv_app_app,
    restrict_map]
  simp only [← Functor.map_comp]
  congr 1

end AlgebraicGeometry.Scheme.Modules
