/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.FreeComp
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Mate

/-!
# Transferring a map into a free sheaf between two pullbacks

Let `π : X ⟶ T` and `p : X ⟶ P` be morphisms of schemes and `ιK : K ⟶ 𝒪_T^I` a morphism into a
free sheaf on `T`. Its transfer

`freeTransfer π p ιK : π^* K ⟶ π^* 𝒪_T^I ≅ 𝒪_X^I ≅ p^* 𝒪_P^I`

uses `pullbackFreeIso` twice. For a commutative square `b ≫ π = π' ≫ g` with `b : X' ⟶ X`,
`π' : X' ⟶ T'`, `g : T' ⟶ T`, the square comparison
`(pullbackSquareIso b π' π g h).app K : π'^* g^* K ≅ b^* π^* K` (`Modules/BaseChange/Affine/Mate`,
built from `pullbackComp` and `pullbackCongr`) carries the pullback along `b` of the transfer of
`ιK` to the transfer of the pulled-back map `g^* ιK ≫ pullbackFreeIso g I : g^* K ⟶ 𝒪_{T'}^I`, for
every `p' = b ≫ p` (`pullbackSquareIso_hom_freeTransfer`). The proof uses the composition and
congruence laws of `pullbackFreeIso` (`pullbackFreeIso_comp`, `pullbackFreeIso_congr`).

No hypothesis on the morphisms or on `K` is needed. Consumer: the map `π^* K(-r) ⟶ 𝒪` of
Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 26,
property (F), in `Aglib.AlgebraicGeometry.HilbertScheme.UniversalSubscheme`, where `K` is a
subsheaf of the free sheaf on the monomials of degree `r`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X T P : Scheme.{u}}

/-- The transfer `π^* K ⟶ π^* 𝒪_T^I ≅ 𝒪_X^I ≅ p^* 𝒪_P^I` of a map `ιK : K ⟶ 𝒪_T^I` along
`π : X ⟶ T` and `p : X ⟶ P`. -/
def freeTransfer (π : X ⟶ T) (p : X ⟶ P) {K : T.Modules} {I : Type u}
    (ιK : K ⟶ SheafOfModules.free (R := T.ringCatSheaf) I) :
    (pullback π).obj K ⟶ (pullback p).obj (SheafOfModules.free (R := P.ringCatSheaf) I) :=
  (pullback π).map ιK ≫ (pullbackFreeIso π I).hom ≫ (pullbackFreeIso p I).inv

/-- **The transfer commutes with base change**: for a commutative square `b ≫ π = π' ≫ g` and
`b ≫ p = p'`, the comparison `pullbackSquareIso : π'^* g^* K ≅ b^* π^* K` followed by the
pullback along `b` of the transfer of `ιK` is the transfer of `g^* ιK ≫ pullbackFreeIso g I`
followed by `p'^* 𝒪^I ≅ (b ≫ p)^* 𝒪^I ≅ b^* p^* 𝒪^I`. -/
theorem pullbackSquareIso_hom_freeTransfer {X' T' : Scheme.{u}} (b : X' ⟶ X) (π : X ⟶ T)
    (π' : X' ⟶ T') (g : T' ⟶ T) (h : b ≫ π = π' ≫ g) (p : X ⟶ P) (p' : X' ⟶ P)
    (hb : b ≫ p = p') {K : T.Modules} {I : Type u}
    (ιK : K ⟶ SheafOfModules.free (R := T.ringCatSheaf) I) :
    ((pullbackSquareIso b π' π g h).app K).hom ≫ (pullback b).map (freeTransfer π p ιK) =
      freeTransfer π' p' ((pullback g).map ιK ≫ (pullbackFreeIso g I).hom) ≫
        (pullbackCongr hb.symm).hom.app (SheafOfModules.free I) ≫
          (pullbackComp b p).inv.app (SheafOfModules.free I) := by
  subst hb
  have hc : (pullbackCongr (rfl : b ≫ p = b ≫ p)).hom = 𝟙 _ := rfl
  rw [hc, NatTrans.id_app, Category.id_comp,
    ← Iso.cancel_iso_hom_right _ _ ((pullback b).mapIso (pullbackFreeIso p I) ≪≫
      pullbackFreeIso b I)]
  simp only [pullbackSquareIso, freeTransfer, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  have h1 : (pullback b).map (pullbackFreeIso p I).inv ≫
      (pullback b).map (pullbackFreeIso p I).hom = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  have h3 := (pullbackComp b π).inv.naturality ιK
  have h5 := (pullbackCongr h.symm).hom.naturality ιK
  have h6 := (pullbackComp π' g).hom.naturality ιK
  dsimp only [Functor.comp_map] at h3 h6
  rw [reassoc_of% h1, ← pullbackFreeIso_comp b π I, ← reassoc_of% h3,
    Iso.inv_hom_id_app_assoc, ← reassoc_of% h5, pullbackFreeIso_congr h.symm I,
    ← reassoc_of% h6, pullbackFreeIso_comp π' g I, ← pullbackFreeIso_comp b p I,
    Iso.inv_hom_id_app_assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Scheme.Modules
