/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.Charts

/-! # Equality transport of the actual local chart comparison

Equal affine chart maps and equal source projections preserve the original
local map through the native open-restriction equality comparisons.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

private theorem restrictFunctorCongr_refl_hom {Y X : Scheme.{u}}
    (j : Y ⟶ X) [IsOpenImmersion j] (M : X.Modules) :
    (restrictFunctorCongr (rfl : j = j)).hom.app M = 𝟙 _ := by
  apply Scheme.Modules.hom_ext
  intro O
  rw [restrictFunctorCongr_hom_app_app]
  change M.presheaf.map (𝟙 (op (j ''ᵁ O))) = 𝟙 _
  exact M.presheaf.map_id _

/-- Equality of chart presentations carries the actual local comparison through the
original restriction equality isomorphism. The cartesian proofs introduce no extra choice. -/
theorem localMap_congr_charts
    {W U V X U₀ W₀ : Scheme.{u}}
    (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
    (h : IsPullback a b f g) [QuasiCompact f] [QuasiSeparated f]
    {R S : CommRingCat.{u}}
    (j j' : Spec R ⟶ X) (v v' : Spec S ⟶ V) (σ σ' : R ⟶ S)
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion v] [IsOpenImmersion v']
    (hv : Spec.map σ ≫ j = v ≫ g) (hv' : Spec.map σ' ≫ j' = v' ≫ g)
    (n : ℕ) (M : U.Modules) [M.IsQuasicoherent]
    (p p' : U₀ ⟶ U) (d : U₀ ⟶ Spec R) [IsOpenImmersion p] [IsOpenImmersion p']
    (hU : IsPullback p d f j) (hU' : IsPullback p' d f j')
    (c c' : W₀ ⟶ W) (e : W₀ ⟶ Spec S) [IsOpenImmersion c] [IsOpenImmersion c']
    (hW : IsPullback c e b v) (hW' : IsPullback c' e b v')
    (q q' : W₀ ⟶ U₀)
    (hqU : q ≫ p = c ≫ a) (hqB : q ≫ d = e ≫ Spec.map σ)
    (hqU' : q' ≫ p' = c' ≫ a) (hqB' : q' ≫ d = e ≫ Spec.map σ')
    (hj : j = j') (ht : v = v') (hσ : σ = σ')
    (hp : p = p') (hc : c = c') (hq : q = q') :
    (restrictFunctorCongr ht).hom.app
        ((pullback g).obj (((pushforward f).rightDerived n).obj M)) ≫
      localMap a b f g h j' v' σ' hv' n M p' d hU' c' e hW' q' hqU' hqB' =
    localMap a b f g h j v σ hv n M p d hU c e hW q hqU hqB ≫
      (restrictFunctorCongr ht).hom.app
        (((pushforward b).rightDerived n).obj ((pullback a).obj M)) := by
  subst j'
  subst v'
  subst σ'
  subst p'
  subst c'
  subst q'
  simp only [restrictFunctorCongr_refl_hom, Category.id_comp, Category.comp_id]

end AlgebraicGeometry.Scheme.Modules.Nonflat
