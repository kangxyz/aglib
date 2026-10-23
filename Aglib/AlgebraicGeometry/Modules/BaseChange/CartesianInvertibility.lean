/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Mate
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Composition
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Pullback

/-!
# Invertibility of the base-change mate does not depend on the cartesian square

For a cartesian square `IsPullback a b f g` and a module `M` on the upper right corner, if the
canonical base-change map `moduleBaseChangeMap f g M` of the chosen pullback is an isomorphism,
then so is the mate `(cartesianBaseChangeMap a b f g h).app M` of the given square
(`isIso_cartesianBaseChangeMap_of_isIso_moduleBaseChangeMap`). The proof compares the square with
the chosen pullback through `IsPullback.isoPullback`: the comparison square has an isomorphism,
hence an open immersion, on top, so its mate is invertible
(`isIso_cartesianBaseChangeMap_of_isOpenImmersion`), and the mates compose
(`cartesianBaseChangeMap_comp`).

No hypothesis on the morphisms or on `M` is needed beyond the invertibility of the chosen map.
Consumers: the base-change isomorphisms of the direct images `π_* 𝒪_Z(r)` and `π_* I_Z(r)` of a
Hilbert family (`HilbertScheme/DirectImageSheafQuotient`, `HilbertScheme/IdealTwist/BaseChange`).
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {W X T S : Scheme.{u}}

/-- **Every cartesian base-change mate is invertible when the chosen one is**: for
`IsPullback a b f g`, if `moduleBaseChangeMap f g M` is an isomorphism, so is
`(cartesianBaseChangeMap a b f g h).app M`. -/
theorem isIso_cartesianBaseChangeMap_of_isIso_moduleBaseChangeMap (a : W ⟶ X) (b : W ⟶ T)
    (f : X ⟶ S) (g : T ⟶ S) (h : IsPullback a b f g) (M : X.Modules)
    (hM : IsIso (moduleBaseChangeMap f g M)) :
    IsIso ((cartesianBaseChangeMap a b f g h).app M) := by
  rw [moduleBaseChangeMap_eq_cartesianBaseChangeMap] at hM
  let e := h.isoPullback
  have hfst : e.hom ≫ Limits.pullback.fst f g = a := h.isoPullback_hom_fst
  have hsnd : e.hom ≫ Limits.pullback.snd f g = b := h.isoPullback_hom_snd
  have h' : IsPullback e.hom b (Limits.pullback.snd f g) (𝟙 T) :=
    IsPullback.of_horiz_isIso ⟨by rw [hsnd, Category.comp_id]⟩
  have H : IsPullback (e.hom ≫ Limits.pullback.fst f g) b f (𝟙 T ≫ g) := by
    rw [hfst, Category.id_comp]
    exact h
  have hcomp := cartesianBaseChangeMap_comp (Limits.pullback.fst f g)
    (Limits.pullback.snd f g) f g (IsPullback.of_hasPullback f g) e.hom b (𝟙 T) h' H M
  have : IsIso ((cartesianBaseChangeMap e.hom b (Limits.pullback.snd f g) (𝟙 T) h').app
      ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj M)) :=
    isIso_cartesianBaseChangeMap_of_isOpenImmersion e.hom b (Limits.pullback.snd f g) (𝟙 T) h' _
  have hH : IsIso ((cartesianBaseChangeMap (e.hom ≫ Limits.pullback.fst f g) b f (𝟙 T ≫ g) H).app
      M) := by
    have : IsIso ((pullbackComp (𝟙 T) g).hom.app ((Scheme.Modules.pushforward f).obj M) ≫
        (cartesianBaseChangeMap (e.hom ≫ Limits.pullback.fst f g) b f (𝟙 T ≫ g) H).app M) := by
      rw [hcomp]
      infer_instance
    exact IsIso.of_isIso_comp_left ((pullbackComp (𝟙 T) g).hom.app _) _
  have htransport (a₁ a₂ : W ⟶ X) (g₁ g₂ : T ⟶ S) (ha : a₁ = a₂) (hg : g₁ = g₂)
      (H₁ : IsPullback a₁ b f g₁) (H₂ : IsPullback a₂ b f g₂) :
      IsIso ((cartesianBaseChangeMap a₁ b f g₁ H₁).app M) ↔
        IsIso ((cartesianBaseChangeMap a₂ b f g₂ H₂).app M) := by
    subst a₂
    subst g₂
    rfl
  exact (htransport _ a _ g hfst (Category.id_comp g) H h).mp hH

end AlgebraicGeometry.Scheme.Modules
