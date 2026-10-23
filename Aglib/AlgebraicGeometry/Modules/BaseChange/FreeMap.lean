/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.FreeMap
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Mate
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Adjoint
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom

/-!
# Maps out of free sheaves under direct image and base change

For a morphism of schemes `π : Y ⟶ X` and `ψ : free I ⟶ M` on `Y`,
`pushforwardFreeMap π ψ : free I ⟶ π_* M` is the adjoint of `π^* free I ≅ free I ⟶ M`. On a
basis inclusion it is the direct image of `ιFree i ≫ ψ` (`ιFree_pushforwardFreeMap`), so on global
sections it sends the basis section `e_i` to the global section of `ιFree i ≫ ψ`
(`unitHomGlobalSectionsEquiv_ιFree_pushforwardFreeMap`). It respects composition on the right
(`pushforwardFreeMap_comp_right`), and `ιK ≫ pushforwardFreeMap π ψ` vanishes exactly when
`π^* ιK ≫ (π^* free I ≅ free I) ≫ ψ` does (`comp_pushforwardFreeMap_eq_zero_iff`). The pullback
counterpart `pullbackFreeMap` is in `Modules/Pullback/FreeMap`.

**Base change.** For a commutative square `a, b, f, g`, the comparison `pullbackSquareIso` on a
free sheaf is compatible with the free isomorphisms (`pullbackFreeIso_square`). For a cartesian
square (`IsPullback a b f g`), a map `ψ` on the upper left corner's base and `ψ'` with
`pullbackFreeMap a ψ ≫ c.hom = ψ'` for `c : a^* M ≅ M'`, the pullback along `g` of
`pushforwardFreeMap f ψ`, followed by the base-change mate `cartesianBaseChangeMap a b f g h` and
`b_* c`, is `pushforwardFreeMap b ψ'` (`pushforwardFreeMap_baseChange`). Invertibility of the mate
of an arbitrary cartesian square is in `Modules/BaseChange/CartesianInvertibility`.

These are the identities used for the quotient `π_{T*} E_T(r) → π_{T*} F(r)` of Nitsure,
*Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 26, with
`E = 𝒪^{monomials}` free: the quotient over `T'` is the pullback of the quotient over `T`.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

section Square

variable {W X T S : Scheme.{u}} {I : Type u}

/-- **The free sheaf along a commutative square**: the comparison
`pullbackSquareIso : b^* g^* ≅ a^* f^*` on `free I` is compatible with the free isomorphisms. -/
theorem pullbackFreeIso_square (a : W ⟶ X) (b : W ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
    (w : a ≫ f = b ≫ g) (I : Type u) :
    (Scheme.Modules.pullback b).map (pullbackFreeIso g I).inv ≫
        (pullbackSquareIso a b f g w).hom.app (SheafOfModules.free I) ≫
          (Scheme.Modules.pullback a).map (pullbackFreeIso f I).hom =
      (pullbackFreeIso b I).hom ≫ (pullbackFreeIso a I).inv := by
  rw [← cancel_mono (pullbackFreeIso a I).hom, Category.assoc, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, ← pullbackFreeIso_comp]
  simp only [pullbackSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Iso.inv_hom_id_app_assoc, pullbackFreeIso_congr, pullbackFreeIso_comp,
    ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- The adjoint `free I ⟶ π_* M` of `π^* free I ≅ free I ⟶ M`. -/
def pushforwardFreeMap (π : X ⟶ S) {M : X.Modules} (ψ : SheafOfModules.free I ⟶ M) :
    SheafOfModules.free (R := S.ringCatSheaf) I ⟶ (Scheme.Modules.pushforward π).obj M :=
  (pullbackPushforwardAdjunction π).homEquiv _ _ ((pullbackFreeIso π I).hom ≫ ψ)

theorem pushforwardFreeMap_def (π : X ⟶ S) {M : X.Modules} (ψ : SheafOfModules.free I ⟶ M) :
    pushforwardFreeMap π ψ =
      (pullbackPushforwardAdjunction π).homEquiv _ _ ((pullbackFreeIso π I).hom ≫ ψ) :=
  rfl

/-- **The basis sections of the adjoint**: `pushforwardFreeMap π ψ` sends the basis inclusion
`ιFree i` to the direct image of `ιFree i ≫ ψ`. -/
theorem ιFree_pushforwardFreeMap (π : X ⟶ S) {M : X.Modules} (ψ : SheafOfModules.free I ⟶ M)
    (i : I) :
    SheafOfModules.ιFree i ≫ pushforwardFreeMap π ψ =
      SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward π).map (SheafOfModules.ιFree i ≫ ψ) := by
  rw [pushforwardFreeMap_def, ← Adjunction.homEquiv_naturality_left,
    pullback_map_ιFree_comp_pullbackFreeIso_hom_assoc, Adjunction.homEquiv_naturality_right]
  congr 1
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _

/-- **The global sections of the adjoint on the basis**: the global section of
`ιFree i ≫ pushforwardFreeMap π ψ` is that of `ιFree i ≫ ψ`. -/
theorem unitHomGlobalSectionsEquiv_ιFree_pushforwardFreeMap (π : X ⟶ S) {M : X.Modules}
    (ψ : SheafOfModules.free I ⟶ M) (i : I) :
    unitHomGlobalSectionsEquiv S ((Scheme.Modules.pushforward π).obj M)
        (SheafOfModules.ιFree i ≫ pushforwardFreeMap π ψ) =
      unitHomGlobalSectionsEquiv X M (SheafOfModules.ιFree i ≫ ψ) := by
  rw [ιFree_pushforwardFreeMap, unitHomGlobalSectionsEquiv_apply,
    unitHomGlobalSectionsEquiv_apply, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  exact congrArg (Scheme.Modules.Hom.app (SheafOfModules.ιFree i ≫ ψ) ⊤)
    (map_one (π.toRingCatSheafHom.hom.app (op ⊤)).hom)

/-- The pullback of the adjoint, followed by the counit, is the original map. -/
@[reassoc]
theorem pullback_map_homEquiv_comp_counit (π : X ⟶ S) {A : S.Modules} {M : X.Modules}
    (k : (Scheme.Modules.pullback π).obj A ⟶ M) :
    (Scheme.Modules.pullback π).map ((pullbackPushforwardAdjunction π).homEquiv _ _ k) ≫
        (pullbackPushforwardAdjunction π).counit.app M = k :=
  ((pullbackPushforwardAdjunction π).homEquiv_counit
    (g := (pullbackPushforwardAdjunction π).homEquiv _ _ k)).symm.trans
      (Equiv.symm_apply_apply _ k)

/-- `pushforwardFreeMap` of a composite: `π_*` of the second map follows. -/
theorem pushforwardFreeMap_comp_right (π : X ⟶ S) {M M' : X.Modules}
    (ψ : SheafOfModules.free I ⟶ M) (k : M ⟶ M') :
    pushforwardFreeMap π (ψ ≫ k) =
      pushforwardFreeMap π ψ ≫ (Scheme.Modules.pushforward π).map k := by
  rw [pushforwardFreeMap_def, pushforwardFreeMap_def, ← Category.assoc,
    Adjunction.homEquiv_naturality_right]

/-- **Vanishing against the adjoint of a map out of a free sheaf**: for `ιK : K ⟶ free I` on `S`
and `ψ : free I ⟶ M` on `X`, the composite of `ιK` with the adjoint `free I ⟶ π_* M` of `ψ`
vanishes exactly when `π^* ιK ≫ (π^* free I ≅ free I) ≫ ψ` does. -/
theorem comp_pushforwardFreeMap_eq_zero_iff (π : X ⟶ S) {M : X.Modules}
    (ψ : SheafOfModules.free I ⟶ M) {K : S.Modules} (ιK : K ⟶ SheafOfModules.free I) :
    ιK ≫ pushforwardFreeMap π ψ = 0 ↔
      (Scheme.Modules.pullback π).map ιK ≫ (pullbackFreeIso π I).hom ≫ ψ = 0 := by
  have h : ιK ≫ pushforwardFreeMap π ψ = (pullbackPushforwardAdjunction π).homEquiv _ _
      ((Scheme.Modules.pullback π).map ιK ≫ (pullbackFreeIso π I).hom ≫ ψ) := by
    rw [pushforwardFreeMap_def, Adjunction.homEquiv_naturality_left]
  rw [h]
  constructor
  · intro h0
    rw [← pullback_map_homEquiv_comp_counit π
      ((Scheme.Modules.pullback π).map ιK ≫ (pullbackFreeIso π I).hom ≫ ψ), h0,
      Functor.map_zero, zero_comp]
  · intro h0
    rw [h0, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]

/-- **Base change of the adjoint of a map out of a free sheaf.** For a cartesian square
`IsPullback a b f g` and maps `ψ`, `ψ'` out of `free I` with `pullbackFreeMap a ψ ≫ c.hom = ψ'`,
the pullback along `g` of `pushforwardFreeMap f ψ`, followed by the base-change mate and `b_* c`,
is `pushforwardFreeMap b ψ'`. -/
theorem pushforwardFreeMap_baseChange (a : W ⟶ X) (b : W ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
    (h : IsPullback a b f g) {M : X.Modules} {M' : W.Modules} (ψ : SheafOfModules.free I ⟶ M)
    (ψ' : SheafOfModules.free I ⟶ M') (c : (Scheme.Modules.pullback a).obj M ≅ M')
    (hψ : pullbackFreeMap a ψ ≫ c.hom = ψ') :
    pullbackFreeMap g (pushforwardFreeMap f ψ) ≫ (cartesianBaseChangeMap a b f g h).app M ≫
        (Scheme.Modules.pushforward b).map c.hom =
      pushforwardFreeMap b ψ' := by
  rw [pullbackFreeMap_def, pushforwardFreeMap_def f ψ, pushforwardFreeMap_def b ψ',
    Category.assoc, reassoc_of% (cartesianBaseChangeMap_adjoint a b f g h
      (SheafOfModules.free I) M ((pullbackFreeIso f I).hom ≫ ψ)),
    ← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left]
  congr 1
  rw [← hψ, pullbackFreeMap_def]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% (pullbackFreeIso_square a b f g h.w I)]

end Square

end AlgebraicGeometry.Scheme.Modules
