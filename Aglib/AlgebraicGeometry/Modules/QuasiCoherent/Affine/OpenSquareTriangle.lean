/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback

/-! # The original open square through a retained direct pullback

The two actual geometric path equalities identify the original open-square
comparison with the original two direct-versus-iterated pullback triangles.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Both original restriction/pullback corrections and both geometric triangles
are retained when expressing the actual open-square comparison. -/
theorem pullbackOpenSquare_direct_triangle
    {W X V Y : Scheme.{u}} (p : W ⟶ X) (q : W ⟶ V) (f : X ⟶ Y) (a : V ⟶ Y)
    [IsOpenImmersion p] [IsOpenImmersion a] (k : W ⟶ Y)
    (hp : p ≫ f = k) (hq : q ≫ a = k) (M : Y.Modules) :
    let βp := (pullbackCongr hp.symm).app M ≪≫ ((pullbackComp p f).app M).symm
    let βq := (pullbackCongr hq.symm).app M ≪≫ ((pullbackComp q a).app M).symm
    (pullbackOpenSquare p q f a (hp.trans hq.symm)).hom.app M ≫
        (pullback q).map ((restrictFunctorIsoPullback a).hom.app M) =
      (restrictFunctorIsoPullback p).hom.app ((pullback f).obj M) ≫ βp.inv ≫ βq.hom := by
  have hγ : (pullbackCongr hp.symm).inv ≫ (pullbackCongr hq.symm).hom =
      (pullbackCongr (hp.trans hq.symm)).hom := by
    simp only [pullbackCongr, eqToIso.inv, eqToIso.hom, eqToHom_trans]
  have hγM : (pullbackCongr hp.symm).inv.app M ≫ (pullbackCongr hq.symm).hom.app M =
      (pullbackCongr (hp.trans hq.symm)).hom.app M := by
    simpa only [NatTrans.comp_app] using congr_app hγ M
  have hqId : (pullback q).map (𝟙 ((pullback a).obj M)) =
      𝟙 ((pullback q).obj ((pullback a).obj M)) :=
    (pullback q).map_id ((pullback a).obj M)
  dsimp only
  simp only [pullbackOpenSquare, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, reassoc_of% hγM]
  rw [hqId]
  have ht : (pullbackComp q a).inv.app M ≫
        𝟙 ((pullback q).obj ((pullback a).obj M)) = (pullbackComp q a).inv.app M :=
    Category.comp_id (obj := W.Modules) ((pullbackComp q a).inv.app M)
  exact congrArg
    (fun z : (pullback (q ≫ a)).obj M ⟶ (pullback q).obj ((pullback a).obj M) =>
      (restrictFunctorIsoPullback p).hom.app ((pullback f).obj M) ≫
        (pullbackComp p f).hom.app M ≫
        (pullbackCongr (hp.trans hq.symm)).hom.app M ≫ z) ht

end AlgebraicGeometry.Scheme.Modules
