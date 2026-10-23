/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Isomorphism
public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.Pullback

/-!
# Pulled-back pairings to the structure module

Let `p : X ⟶ P` be a morphism of schemes and `ε : N ⊗ L ⟶ 𝒪_P` a morphism of `𝒪_P`-modules
(a pairing). Its pullback along `p` is the pairing

`pullbackPairing p ε : p^* N ⊗ p^* L ≅ p^*(N ⊗ L) ⟶ p^* 𝒪_P ≅ 𝒪_X`,

through the inverse of the canonical tensor comparison `pullbackTensorMap p N L`
(`pullbackTensorMapIso`, an isomorphism for every morphism and all modules) and
`pullbackUnitIso p`. For a module `M` on `X` and `j : M ⟶ p^* N`,
`pullbackPairingOf p ε j : M ⊗ p^* L ⟶ 𝒪_X` is `j ⊗ 𝟙` followed by `pullbackPairing p ε`.

* `pullback_map_pullbackPairing`: for `b : X' ⟶ X`, the pullback of `pullbackPairing p ε` along
  `b` is `pullbackPairing (b ≫ p) ε` under the comparisons `b^* p^* ≅ (b ≫ p)^*`. The proof uses
  the composition law of the tensor comparison (`PowerPullback.pullbackTensorMap_comp`) and of the
  unit comparison (`pullbackUnitIso_comp`).
* `pullbackPairingOf_pullback`: for `b : X' ⟶ X`, `p' = b ≫ p`, and maps `c : M' ⟶ b^* M`,
  `j' : M' ⟶ p'^* N` with `c ≫ b^* j = j'` under `p'^* N ≅ b^* p^* N`, the pairing
  `pullbackPairingOf p' ε j'` is `c ⊗ (p'^* L ≅ b^* p^* L)` followed by the pullback along `b` of
  `pullbackPairingOf p ε j`.

No flatness, finiteness or quasi-coherence is assumed. These are the base-change compatibilities
of the map `π^* K(-r) ⟶ 𝒪` of Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, §5, p. 26, property (F), consumed by
`Aglib.AlgebraicGeometry.HilbertScheme.UniversalSubscheme`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The canonical tensor comparison `f^*(M ⊗ N) ≅ f^* M ⊗ f^* N` as an isomorphism
(`Pullback.Tensor.pullbackTensorMap_isIso`). -/
def pullbackTensorMapIso (f : X ⟶ Y) (M N : Y.Modules) :
    (pullback f).obj (tensorSheaf Y M N) ≅
      (show X.Modules from tensorSheaf X ((pullback f).obj M) ((pullback f).obj N)) :=
  haveI := Pullback.Tensor.pullbackTensorMap_isIso f M N
  asIso (pullbackTensorMap f M N)

@[simp]
theorem pullbackTensorMapIso_hom (f : X ⟶ Y) (M N : Y.Modules) :
    (pullbackTensorMapIso f M N).hom = pullbackTensorMap f M N :=
  rfl

/-- The inverse of the tensor comparison is natural in both factors. -/
@[reassoc]
theorem pullbackTensorMapIso_inv_naturality (f : X ⟶ Y) {M M' N N' : Y.Modules}
    (a : M ⟶ M') (c : N ⟶ N') :
    (pullbackTensorMapIso f M N).inv ≫ (pullback f).map (tensorSheafMap Y a c) =
      tensorSheafMap X ((pullback f).map a) ((pullback f).map c) ≫
        (pullbackTensorMapIso f M' N').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  simp only [pullbackTensorMapIso_hom]
  exact pullbackTensorMap_naturality f a c

/-- The forward map of main's tensor product of isomorphisms `tensorSheafIso`
(`Modules/Tensor/Basic`) is `tensorSheafMap X e.hom e'.hom`, definitionally. -/
@[simp]
theorem tensorSheafIso_hom {M M' N N' : X.Modules} (e : M ≅ M') (e' : N ≅ N') :
    (tensorSheafIso X e e').hom = tensorSheafMap X e.hom e'.hom :=
  rfl

/-- The inverse map of `tensorSheafIso` is `tensorSheafMap X e.inv e'.inv`, definitionally. -/
@[simp]
theorem tensorSheafIso_inv {M M' N N' : X.Modules} (e : M ≅ M') (e' : N ≅ N') :
    (tensorSheafIso X e e').inv = tensorSheafMap X e.inv e'.inv :=
  rfl

variable {P : Scheme.{u}} (p : X ⟶ P) {N L : P.Modules}

/-- **The pullback of a pairing** `ε : N ⊗ L ⟶ 𝒪_P` along `p : X ⟶ P`:
`p^* N ⊗ p^* L ≅ p^*(N ⊗ L) ⟶ p^* 𝒪_P ≅ 𝒪_X`. -/
def pullbackPairing
    (ε : (show P.Modules from tensorSheaf P N L) ⟶
      (show P.Modules from SheafOfModules.unit P.ringCatSheaf)) :
    (show X.Modules from tensorSheaf X ((pullback p).obj N) ((pullback p).obj L)) ⟶
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) :=
  (pullbackTensorMapIso p N L).inv ≫ (pullback p).map ε ≫ (pullbackUnitIso p).hom

/-- The pulled-back pairing after the tensor comparison is the pullback of the pairing. -/
@[reassoc]
theorem pullbackTensorMap_pullbackPairing
    (ε : (show P.Modules from tensorSheaf P N L) ⟶
      (show P.Modules from SheafOfModules.unit P.ringCatSheaf)) :
    pullbackTensorMap p N L ≫ pullbackPairing p ε =
      (pullback p).map ε ≫ (pullbackUnitIso p).hom := by
  rw [pullbackPairing, ← pullbackTensorMapIso_hom, Iso.hom_inv_id_assoc]

/-- **Pullback of a pulled-back pairing**: for `b : X' ⟶ X`, the pullback along `b` of
`pullbackPairing p ε`, followed by `pullbackUnitIso b`, is the tensor comparison of `b` followed by
`b^* p^* ≅ (b ≫ p)^*` on both factors and `pullbackPairing (b ≫ p) ε`. -/
theorem pullback_map_pullbackPairing {X' : Scheme.{u}} (b : X' ⟶ X)
    (ε : (show P.Modules from tensorSheaf P N L) ⟶
      (show P.Modules from SheafOfModules.unit P.ringCatSheaf)) :
    (pullback b).map (pullbackPairing p ε) ≫ (pullbackUnitIso b).hom =
      pullbackTensorMap b ((pullback p).obj N) ((pullback p).obj L) ≫
        tensorSheafMap X' ((pullbackComp b p).hom.app N) ((pullbackComp b p).hom.app L) ≫
          pullbackPairing (b ≫ p) ε := by
  let E : (pullback (b ≫ p)).obj (tensorSheaf P N L) ≅
      (pullback b).obj (tensorSheaf X ((pullback p).obj N) ((pullback p).obj L)) :=
    ((pullbackComp b p).app (tensorSheaf P N L)).symm ≪≫
      (pullback b).mapIso (pullbackTensorMapIso p N L)
  have hE : E.hom = (pullbackComp b p).inv.app (tensorSheaf P N L) ≫
      (pullback b).map (pullbackTensorMap p N L) := rfl
  rw [← Iso.cancel_iso_hom_left E, hE]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, pullbackTensorMap_pullbackPairing, Functor.map_comp_assoc]
  have hn := (pullbackComp b p).inv.naturality ε
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, ← pullbackUnitIso_comp b p, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% (Invertible.PowerPullback.pullbackTensorMap_comp b p N L),
    tensorSheafMap_comp_assoc, Iso.inv_hom_id_app, Iso.inv_hom_id_app,
    Invertible.PowerPullback.tensorSheafMap_id, Category.id_comp,
    pullbackTensorMap_pullbackPairing]

/-- `pullback_map_pullbackPairing` in inverse form. -/
theorem pullbackTensorMapIso_inv_pullback_map_pullbackPairing {X' : Scheme.{u}} (b : X' ⟶ X)
    (ε : (show P.Modules from tensorSheaf P N L) ⟶
      (show P.Modules from SheafOfModules.unit P.ringCatSheaf)) :
    (pullbackTensorMapIso b ((pullback p).obj N) ((pullback p).obj L)).inv ≫
        (pullback b).map (pullbackPairing p ε) ≫ (pullbackUnitIso b).hom =
      tensorSheafMap X' ((pullbackComp b p).hom.app N) ((pullbackComp b p).hom.app L) ≫
        pullbackPairing (b ≫ p) ε := by
  rw [Iso.inv_comp_eq, pullbackTensorMapIso_hom]
  exact pullback_map_pullbackPairing p b ε

/-- The pairing `M ⊗ p^* L ⟶ 𝒪_X` of a map `j : M ⟶ p^* N`: `j ⊗ 𝟙` followed by
`pullbackPairing p ε`. -/
def pullbackPairingOf
    (ε : (show P.Modules from tensorSheaf P N L) ⟶
      (show P.Modules from SheafOfModules.unit P.ringCatSheaf))
    {M : X.Modules} (j : M ⟶ (pullback p).obj N) :
    (show X.Modules from tensorSheaf X M ((pullback p).obj L)) ⟶
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) :=
  tensorSheafMap X j (𝟙 ((pullback p).obj L)) ≫ pullbackPairing p ε

/-- **Base change of the pairing of a map**: for `b : X' ⟶ X` and `p' : X' ⟶ P` with
`b ≫ p = p'`, and maps `c : M' ⟶ b^* M`, `j' : M' ⟶ p'^* N` with `c ≫ b^* j = j'` under
`p'^* N ≅ b^* p^* N`, the pairing of `j'` is `c ⊗ (p'^* L ≅ b^* p^* L)`, then the inverse tensor
comparison of `b`, then the pullback along `b` of the pairing of `j` and `pullbackUnitIso b`. -/
theorem pullbackPairingOf_pullback {X' : Scheme.{u}} (b : X' ⟶ X) (p' : X' ⟶ P)
    (hb : b ≫ p = p')
    (ε : (show P.Modules from tensorSheaf P N L) ⟶
      (show P.Modules from SheafOfModules.unit P.ringCatSheaf))
    {M : X.Modules} (j : M ⟶ (pullback p).obj N) {M' : X'.Modules}
    (c : M' ⟶ (pullback b).obj M) (j' : M' ⟶ (pullback p').obj N)
    (hj : c ≫ (pullback b).map j =
      j' ≫ (pullbackCongr hb.symm).hom.app N ≫ (pullbackComp b p).inv.app N) :
    tensorSheafMap X' c ((pullbackCongr hb.symm).hom.app L ≫ (pullbackComp b p).inv.app L) ≫
        (pullbackTensorMapIso b M ((pullback p).obj L)).inv ≫
          (pullback b).map (pullbackPairingOf p ε j) ≫ (pullbackUnitIso b).hom =
      pullbackPairingOf p' ε j' := by
  subst hb
  have hc : (pullbackCongr (rfl : b ≫ p = b ≫ p)).hom = 𝟙 _ := rfl
  rw [hc] at hj ⊢
  simp only [NatTrans.id_app, Category.id_comp] at hj ⊢
  simp only [pullbackPairingOf, Functor.map_comp, Category.assoc]
  rw [pullbackTensorMapIso_inv_naturality_assoc,
    pullbackTensorMapIso_inv_pullback_map_pullbackPairing, tensorSheafMap_comp_assoc,
    tensorSheafMap_comp_assoc, hj]
  congr 2
  · rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  · erw [CategoryTheory.Functor.map_id, Category.comp_id, Iso.inv_hom_id_app]

end AlgebraicGeometry.Scheme.Modules
