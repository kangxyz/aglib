/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Mate

/-!
# Base change of the counit of the pullback-pushforward adjunction

For a cartesian square `a : W ⟶ X`, `b : W ⟶ T`, `f : X ⟶ S`, `g : T ⟶ S` and a module `M` on
`X`, the pullback along `a` of the counit `f^* f_* M ⟶ M` is the counit `b^* b_* a^* M ⟶ a^* M`
after the base-change map `g^* f_* M ⟶ b_* a^* M` (`cartesianBaseChangeMap`) and the pullback
square isomorphism `b^* g^* ≅ a^* f^*` (`pullback_counit_eq_of_isPullback`, from
`cartesianBaseChangeMap_eq_counit`). When the base-change map is invertible, for instance when
`g` is an open immersion (`isIso_cartesianBaseChangeMap_of_isOpenImmersion`), the pullback of the
counit is an epimorphism as soon as the base-changed counit is
(`epi_pullback_counit_of_isPullback`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {W X T S : Scheme.{u}} (a : W ⟶ X) (b : W ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
  (h : IsPullback a b f g)

/-- **The pullback of the counit along a cartesian square**: `a^*` of the counit of `f` at `M`,
after the pullback square isomorphism, is the pullback along `b` of the base-change map followed
by the counit of `b` at `a^* M`. -/
theorem pullback_counit_eq_of_isPullback (M : X.Modules) :
    (pullback b).map ((cartesianBaseChangeMap a b f g h).app M) ≫
        (pullbackPushforwardAdjunction b).counit.app ((pullback a).obj M) =
      (pullbackSquareIso a b f g h.w).hom.app ((pushforward f).obj M) ≫
        (pullback a).map ((pullbackPushforwardAdjunction f).counit.app M) := by
  calc _ = ((pullbackPushforwardAdjunction b).homEquiv _ _).symm
        ((cartesianBaseChangeMap a b f g h).app M) :=
      ((pullbackPushforwardAdjunction b).homEquiv_counit _ _ _).symm
    _ = _ := by
      rw [cartesianBaseChangeMap_eq_counit a b f g h M]
      exact Equiv.symm_apply_apply _ _

/-- **Base change of an epimorphic counit**: for a cartesian square with invertible base-change
map at `M`, if the counit of `b` at `a^* M` is an epimorphism, so is the pullback along `a` of the
counit of `f` at `M`. -/
theorem epi_pullback_counit_of_isPullback (M : X.Modules)
    [IsIso ((cartesianBaseChangeMap a b f g h).app M)]
    [Epi ((pullbackPushforwardAdjunction b).counit.app ((pullback a).obj M))] :
    Epi ((pullback a).map ((pullbackPushforwardAdjunction f).counit.app M)) := by
  have : Epi ((pullbackSquareIso a b f g h.w).hom.app ((pushforward f).obj M) ≫
      (pullback a).map ((pullbackPushforwardAdjunction f).counit.app M)) := by
    rw [← pullback_counit_eq_of_isPullback a b f g h M]
    infer_instance
  exact epi_of_epi ((pullbackSquareIso a b f g h.w).hom.app ((pushforward f).obj M)) _

end AlgebraicGeometry.Scheme.Modules
