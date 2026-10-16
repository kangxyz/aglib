/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Basic
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Cartesian
public import Aglib.CategoryTheory.Adjunction.MateHomEquiv

/-! # Normalization of the canonical module base-change mate

The original counit-defined map is the mate of the original pushforward square.
These comparisons retain its actual adjunction units and counits.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {W X T S : Scheme.{u}}

/-- Equality of scheme morphisms preserves the original pullback/pushforward adjunction. -/
theorem conjugateEquiv_pullbackCongr {f g : X ⟶ S} (h : f = g) :
    conjugateEquiv (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction f)
      (pullbackCongr h).hom = (pushforwardCongr h).inv := by
  subst g
  change conjugateEquiv _ _ (𝟙 _) = _
  rw [conjugateEquiv_id]
  apply NatTrans.ext
  funext M
  apply Scheme.Modules.hom_ext
  intro U
  simp

/-- The pullback composition comparison of an actual commutative square. -/
def pullbackSquareIso (a : W ⟶ X) (b : W ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
    (h : a ≫ f = b ≫ g) : pullback g ⋙ pullback b ≅ pullback f ⋙ pullback a :=
  pullbackComp b g ≪≫ pullbackCongr h.symm ≪≫ (pullbackComp a f).symm

/-- The actual pullback square is conjugate to the original pushforward square. -/
theorem conjugateEquiv_pullbackSquareIso (a : W ⟶ X) (b : W ⟶ T)
    (f : X ⟶ S) (g : T ⟶ S) (h : IsPullback a b f g) :
    conjugateEquiv
      ((pullbackPushforwardAdjunction f).comp (pullbackPushforwardAdjunction a))
      ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction b))
      (pullbackSquareIso a b f g h.w).hom =
    (cartesianPushforwardSquare a b f g h).hom := by
  have ha := conjugateEquiv_pullbackComp_inv a f
  have hb := conjugateEquiv_pullbackComp_inv b g
  have hc := conjugateEquiv_pullbackCongr h.w.symm
  have he := conjugateEquiv_comp
    ((pullbackPushforwardAdjunction f).comp (pullbackPushforwardAdjunction a))
    (pullbackPushforwardAdjunction (a ≫ f))
    (pullbackPushforwardAdjunction (b ≫ g))
    (pullbackComp a f).inv (pullbackCongr h.w.symm).hom
  rw [ha, hc] at he
  have hd := conjugateEquiv_comp
    ((pullbackPushforwardAdjunction f).comp (pullbackPushforwardAdjunction a))
    (pullbackPushforwardAdjunction (b ≫ g))
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction b))
    ((pullbackCongr h.w.symm).hom ≫ (pullbackComp a f).inv)
    (pullbackComp b g).hom
  rw [← he] at hd
  have hi : conjugateEquiv (pullbackPushforwardAdjunction (b ≫ g))
      ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction b))
      (pullbackComp b g).hom = (pushforwardComp b g).inv := by
    apply (cancel_mono (pushforwardComp b g).hom).mp
    rw [Iso.inv_hom_id]
    rw [← hb, conjugateEquiv_comp]
    simp
  rw [hi] at hd
  have hh : (pushforwardCongr h.w.symm).inv = (pushforwardCongr h.w).hom := by
    apply NatTrans.ext
    funext M
    apply Scheme.Modules.hom_ext
    intro U
    rfl
  rw [hh] at hd
  simpa only [pullbackSquareIso, cartesianPushforwardSquare, Iso.trans_hom,
    Iso.symm_hom, Category.assoc] using hd.symm

/-- The pushforward-square mate is also the actual pullback-square counit mate. -/
theorem cartesianBaseChangeMap_eq_counit (a : W ⟶ X) (b : W ⟶ T)
    (f : X ⟶ S) (g : T ⟶ S) (h : IsPullback a b f g) (M : X.Modules) :
    (cartesianBaseChangeMap a b f g h).app M =
      (pullbackPushforwardAdjunction b).homEquiv _ _
        ((pullbackSquareIso a b f g h.w).hom.app ((pushforward f).obj M) ≫
          (pullback a).map ((pullbackPushforwardAdjunction f).counit.app M)) := by
  have he := iterated_mateEquiv_conjugateEquiv
    (pullbackPushforwardAdjunction f) (pullbackPushforwardAdjunction b)
    (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction a)
    (TwoSquare.mk _ _ _ _ (pullbackSquareIso a b f g h.w).hom)
  rw [conjugateEquiv_pullbackSquareIso a b f g h] at he
  have hh := congrArg (fun z => ((mateEquiv (pullbackPushforwardAdjunction a)
      (pullbackPushforwardAdjunction g)).symm (TwoSquare.mk _ _ _ _ z)).natTrans) he
  simp only [Equiv.symm_apply_apply] at hh
  change (mateEquiv (pullbackPushforwardAdjunction f) (pullbackPushforwardAdjunction b)
      (TwoSquare.mk _ _ _ _ (pullbackSquareIso a b f g h.w).hom)).natTrans =
    cartesianBaseChangeMap a b f g h at hh
  rw [← hh]
  simp [mateEquiv, Adjunction.homEquiv_apply]

/-- The original map agrees with the native cartesian base-change transformation. -/
theorem moduleBaseChangeMap_eq_cartesianBaseChangeMap (f : X ⟶ S) (g : T ⟶ S)
    (M : X.Modules) :
    moduleBaseChangeMap f g M =
      (cartesianBaseChangeMap (Limits.pullback.fst f g) (Limits.pullback.snd f g)
        f g (IsPullback.of_hasPullback f g)).app M := by
  rw [cartesianBaseChangeMap_eq_counit]
  rfl

/-- The actual canonical map preserves the original geometric adjunction units. -/
theorem moduleBaseChangeMap_unit (f : X ⟶ S) (g : T ⟶ S) (M : X.Modules) :
    (pushforward f).map
        ((pullbackPushforwardAdjunction (Limits.pullback.fst f g)).unit.app M) ≫
      (cartesianPushforwardSquare (Limits.pullback.fst f g) (Limits.pullback.snd f g)
        f g (IsPullback.of_hasPullback f g)).hom.app
          ((pullback (Limits.pullback.fst f g)).obj M) =
    (pullbackPushforwardAdjunction g).unit.app ((pushforward f).obj M) ≫
      (pushforward g).map (moduleBaseChangeMap f g M) := by
  rw [moduleBaseChangeMap_eq_cartesianBaseChangeMap]
  exact cartesianBaseChangeMap_unit _ _ _ _ _ M

end AlgebraicGeometry.Scheme.Modules
