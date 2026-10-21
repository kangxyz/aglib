/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Restriction.OverlapRefinement

/-! # Quotient squares on a cartesian presentation of an overlap -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Compatible maps to modules on a cartesian chart presentation give the
original quotient square on the chosen categorical overlap. -/
theorem overlapRestrictIso_refinement_quotient
    {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V)
    (j : U ⟶ X) (k : V ⟶ X) (c : W ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j]
    [IsOpenImmersion k] [IsOpenImmersion c]
    (H : IsPullback a b j k) (ha : a ≫ j = c) (hb : b ≫ k = c)
    (M : X.Modules) (QU : U.Modules) (QV : V.Modules) (QW : W.Modules)
    (qU : M.restrict j ⟶ QU) (qV : M.restrict k ⟶ QV)
    (qW : M.restrict c ⟶ QW)
    (dU : QU.restrict a ≅ QW) (dV : QV.restrict b ≅ QW)
    (hU : (restrictFunctor a).map qU ≫ dU.hom =
      ((restrictFunctorComp a j).symm.app M ≪≫ (restrictFunctorCongr ha).app M).hom ≫ qW)
    (hV : (restrictFunctor b).map qV ≫ dV.hom =
      ((restrictFunctorComp b k).symm.app M ≪≫ (restrictFunctorCongr hb).app M).hom ≫ qW) :
    let l := H.isoPullback.inv
    let eU := (restrictFunctorCongr H.isoPullback_inv_fst).symm.app QU ≪≫
      (restrictFunctorComp l a).app QU
    let eV := (restrictFunctorCongr H.isoPullback_inv_snd).symm.app QV ≪≫
      (restrictFunctorComp l b).app QV
    (restrictFunctor (pullback.fst j k)).map qU ≫
        (eU ≪≫ (restrictFunctor l).mapIso (dU ≪≫ dV.symm) ≪≫ eV.symm).hom =
      (overlapRestrictIso j k).hom.app M ≫
        (restrictFunctor (pullback.snd j k)).map qV := by
  let l := H.isoPullback.inv
  let L := restrictFunctor l
  let rU := (restrictFunctorComp a j).symm.app M ≪≫ (restrictFunctorCongr ha).app M
  let rV := (restrictFunctorComp b k).symm.app M ≪≫ (restrictFunctorCongr hb).app M
  let EU := (restrictFunctorCongr H.isoPullback_inv_fst).symm ≪≫ restrictFunctorComp l a
  let EV := (restrictFunctorCongr H.isoPullback_inv_snd).symm ≪≫ restrictFunctorComp l b
  have hmid : (restrictFunctor a).map qU ≫ (dU ≪≫ dV.symm).hom =
      (rU ≪≫ rV.symm).hom ≫ (restrictFunctor b).map qV := by
    apply (cancel_mono dV.hom).1
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    rw [hU, hV]
    change rU.hom ≫ qW = rU.hom ≫ rV.inv ≫ rV.hom ≫ qW
    rw [Iso.inv_hom_id_assoc]
  have hnU := EU.hom.naturality qU
  have hnV := EV.inv.naturality qV
  dsimp only [Functor.comp_map] at hnU hnV
  have hambient := overlapRestrictIso_refinement a b j k c H ha hb M
  change (EU.hom.app (M.restrict j) ≫ L.map (rU ≪≫ rV.symm).hom ≫
    EV.inv.app (M.restrict k)) = (overlapRestrictIso j k).hom.app M at hambient
  change (restrictFunctor (pullback.fst j k)).map qU ≫
      (EU.hom.app QU ≫ L.map (dU ≪≫ dV.symm).hom ≫ EV.inv.app QV) = _
  calc
    _ = EU.hom.app (M.restrict j) ≫
        L.map ((restrictFunctor a).map qU ≫ (dU ≪≫ dV.symm).hom) ≫
        EV.inv.app QV := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← Category.assoc, hnU]
      simp only [L, Category.assoc]
    _ = (EU.hom.app (M.restrict j) ≫ L.map (rU ≪≫ rV.symm).hom ≫
        EV.inv.app (M.restrict k)) ≫
        (restrictFunctor (pullback.snd j k)).map qV := by
      rw [hmid, Functor.map_comp]
      simp only [Category.assoc]
      rw [hnV]
    _ = _ := by rw [hambient]

end AlgebraicGeometry.Scheme.Modules
