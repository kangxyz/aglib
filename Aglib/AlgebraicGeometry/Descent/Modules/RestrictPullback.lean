/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Restriction and pullback along composite open immersions

Mathlib's `Scheme.Modules.restrictFunctorIsoPullback f` identifies restriction along an open
immersion `f` with the pullback functor, as the uniqueness isomorphism of left adjoints of
`pushforward f`. This file proves that these isomorphisms are compatible with the composition
isomorphisms `restrictFunctorComp` and `pullbackComp`, and with `restrictFunctorCongr` and
`pullbackCongr`.

* `restrictAdjunction_comp_unit_app`: the unit of restriction along `f ≫ g` is the composite of
  the units along `g` and `f`, through `restrictFunctorComp` and `pushforwardComp`.
* `restrictFunctorIsoPullback_comp_hom_app`: the two identifications of `restrict (f ≫ g)` with
  `pullback g ⋙ pullback f` agree.
* `restrictFunctorIsoPullback_congr_hom_app`: the analogous statement for equal morphisms.

Intended owner: `Aglib/AlgebraicGeometry/Modules/Pullback/OpenRestriction.lean` (or Mathlib's
`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`, beside `restrictFunctorIsoPullback`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

section

variable (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]

/-- The unit of the restriction adjunction along `f ≫ g`, followed by `restrictFunctorComp`, is
the composite of the units along `g` and `f`. -/
lemma restrictAdjunction_comp_unit_app (M : Z.Modules) :
    (restrictAdjunction (f ≫ g)).unit.app M ≫
        (pushforward (f ≫ g)).map ((restrictFunctorComp f g).hom.app M) =
      (restrictAdjunction g).unit.app M ≫
        (pushforward g).map ((restrictAdjunction f).unit.app ((restrictFunctor g).obj M)) ≫
          (pushforwardComp f g).hom.app _ := by
  have key : ∀ {V₁ V₂ V₃ V₄ : Z.Opensᵒᵖ} (a : V₁ ⟶ V₂) (a' : V₂ ⟶ V₃) (b : V₁ ⟶ V₄)
      (c : V₄ ⟶ V₃), M.presheaf.map a ≫ M.presheaf.map a' =
        M.presheaf.map b ≫ M.presheaf.map c ≫ 𝟙 _ := fun a a' b c ↦ by
    rw [Category.comp_id, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  ext U : 1
  simp only [Hom.comp_app, pushforward_map_app, restrictAdjunction_unit_app_app,
    restrictFunctorComp_hom_app_app, pushforwardComp_hom_app_app]
  rw [restrict_map]
  exact key _ _ _ _

/-- `restrictFunctorIsoPullback` is compatible with composition: the two identifications of
restriction along `f ≫ g` with `pullback g ⋙ pullback f` agree. -/
lemma restrictFunctorIsoPullback_comp_hom_app (M : Z.Modules) :
    (restrictFunctorIsoPullback (f ≫ g)).hom.app M ≫ (pullbackComp f g).inv.app M =
      (restrictFunctorComp f g).hom.app M ≫
        (restrictFunctor f).map ((restrictFunctorIsoPullback g).hom.app M) ≫
          (restrictFunctorIsoPullback f).hom.app ((pullback g).obj M) := by
  apply ((restrictAdjunction (f ≫ g)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have h₁ := unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv M
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h₁
  have hg : (restrictAdjunction g).unit.app M ≫
      (pushforward g).map ((restrictFunctorIsoPullback g).hom.app M) =
        (pullbackPushforwardAdjunction g).unit.app M :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ _
  have hf : (restrictAdjunction f).unit.app ((restrictFunctor g).obj M) ≫
      (pushforward f).map ((restrictFunctor f).map ((restrictFunctorIsoPullback g).hom.app M)) ≫
        (pushforward f).map ((restrictFunctorIsoPullback f).hom.app ((pullback g).obj M)) =
      (restrictFunctorIsoPullback g).hom.app M ≫
        (pullbackPushforwardAdjunction f).unit.app ((pullback g).obj M) := by
    have := (restrictAdjunction f).unit.naturality ((restrictFunctorIsoPullback g).hom.app M)
    dsimp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at this
    rw [← reassoc_of% this]
    congr 1
    exact Adjunction.unit_leftAdjointUniq_hom_app _ _ _
  have hfg : (restrictAdjunction (f ≫ g)).unit.app M ≫
      (pushforward (f ≫ g)).map ((restrictFunctorIsoPullback (f ≫ g)).hom.app M) =
        (pullbackPushforwardAdjunction (f ≫ g)).unit.app M :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ _
  rw [reassoc_of% hfg, ← h₁, reassoc_of% (restrictAdjunction_comp_unit_app f g M)]
  have n₁ := (pushforwardComp f g).hom.naturality
    ((restrictFunctor f).map ((restrictFunctorIsoPullback g).hom.app M))
  have n₂ := (pushforwardComp f g).hom.naturality
    ((restrictFunctorIsoPullback f).hom.app ((pullback g).obj M))
  dsimp only [Functor.comp_map] at n₁ n₂
  rw [← reassoc_of% n₁, ← n₂]
  have hf' := congrArg (pushforward g).map hf
  simp only [Functor.map_comp, Category.assoc] at hf' ⊢
  rw [reassoc_of% hf', reassoc_of% hg]
  rfl

end

/-- `restrictFunctorIsoPullback` is compatible with `restrictFunctorCongr` and
`pullbackCongr`. -/
lemma restrictFunctorIsoPullback_congr_hom_app {f g : X ⟶ Y} (h : f = g) [IsOpenImmersion f]
    [IsOpenImmersion g] (M : Y.Modules) :
    (restrictFunctorIsoPullback f).hom.app M ≫ (pullbackCongr h).hom.app M =
      (restrictFunctorCongr h).hom.app M ≫ (restrictFunctorIsoPullback g).hom.app M := by
  subst h
  have : (restrictFunctorCongr (rfl : f = f)).hom.app M = 𝟙 _ := by
    ext U : 1
    simp only [restrictFunctorCongr_hom_app_app, eqToHom_refl, op_id, Hom.id_app]
    exact M.presheaf.map_id _
  rw [this, Category.id_comp]
  simp [pullbackCongr]

end AlgebraicGeometry.Scheme.Modules
